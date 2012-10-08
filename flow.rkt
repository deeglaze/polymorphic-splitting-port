#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Polymorphic Flow Analysis

(require "library.rkt"
         "data.rkt"
         "env.rkt"
         "free.rkt"
         "intset.rkt"
         "unparse.rkt"
         "used-before.rkt"
         "abstract.rkt"
         "contour.rkt"
         "callmap.rkt"
         "flags.rkt"
         "mutrec.rkt")

(provide analyse)

;; Statistics Collection
(set-running-time! 0)
(set-starting-time! 0)

(define init-statistics!
  (lambda ()
    (set-running-time! 0)
    (set-starting-time! (current-inexact-milliseconds))))

(define finish-statistics!
  (lambda ()
    (set-running-time! (- (current-inexact-milliseconds) starting-time))
    (printf "Analyzing took ~a ms~%" running-time)
    running-time))

(define analyse
  (lambda ()

    (set! memo-propagate (memo-rec propagate propagate-compare))
    (set! memo-make-read-result (memo make-read-result))
    (set! memo-make-recursive-list (memo make-recursive-list))
    (set! memo-make-ap-get-args (memo make-ap-get-args))

    ;; Label the tree and initialize global data structures.
    (let ([initial-contour (make-initial-contour)])
      (prepare initial-contour)
      (init-abstract!)
      (init-call-map!)

      (init-statistics!)
      (init-abstract-statistics!)

      ;; Here we go!
      (propagate tree (make-context initial-contour aenv-empty) aenv-empty)
      (propagate-across-edges!)

      ;; Return the analysis time.
      (finish-statistics!))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Labels

(define read-like-procedures (list %read %eval %get %expand-once))

;; Add labels to expressions.
(define prepare
  (lambda (initial-contour)
    (define (note-variable! x)
      (unless (or (Name-primitive? x) (memq x variables))
        (set-variables! (cons x variables))))
    (define labels '())
    (define fresh-label
      (let ([label-counter (generate-counter 0)])
        (lambda (e)
          (begin0 (label-counter)
                  (set! labels (cons e labels))))))
    (define read-labels (list initial-contour (fresh-label #f) (fresh-label #f)))
    (define (prepare e recursive)
      ;; recursive is a list of names whose recursive definitions we are currently inside
      (let ([prep (lambda (e) (prepare e recursive))])
        (match e
          [(Define x e1)
           (note-variable! x)
           (prepare e1 (append (or (Name-component x) '()) recursive))]
          [(? Defstruct?) #f]
          [(? Defmacro?) #f]
          [(E: (? Const?))
           (set-E-labels! e (list (fresh-label e)))]
          [(E: (Var x))
           (note-variable! x)
           (define l (fresh-label e))
           (define ls
             (cond [(Name-primitive? x)
                    ;; Most primitives need one "result" label.
                    (cond [(memq x read-like-procedures)
                           read-labels]
                          [(or (Selector? (Name-primop x))
                               (eq? x %internal-apply))
                           '()]
                          [(eq? x %Qmerge-list)
                           (list (fresh-label #f) (fresh-label #f))]
                          [else
                           (list (fresh-label #f))])]
                   [else
                    ;; For non-primitives, the second "label"
                    ;; marks whether this occurrence is recursive.
                    ;; This should be determined by the parser.
                    (list (and (Name-let-bound? x)
                               (not (Name-mutated? x))
                               (memq x recursive)))]))
           (set-E-labels! e (cons l ls))]
          [(E: (Lam: x e1))
           (prep e1)
           (for ([id (in-list x)]) (note-variable! id))
           (set-E-labels! e (list (fresh-label e)))]
          [(E: (Vlam: x rest e1))
           (prep e1)
           (for ([id (in-list (cons rest x))]) (note-variable! id))
           (set-E-labels! e (list (fresh-label e)))]
          [(E: (App e0 args))
           (prep e0)
           (for ([arg (in-list args)]) (prep arg))
           (define l (fresh-label e))
           (define ls
             (for/list ([_ (in-list (list* #f #f args))])
               (fresh-label #f)))
           (set-E-labels! e (cons l ls))]
          [(E: (Let b e2))
           (for ([cl (in-list b)]) (prep cl))
           (prep e2)
           (set-E-labels! e (list (labelof e2)))]
          [(E: (Letr b e2))
           (mark-used-before-defined! b)
           (for ([cl (in-list b)]) (prep cl))
           (prep e2)
           (set-E-labels! e (list (labelof e2)))]
          [(E: (Begin exps))
           (for ([e (in-list exps)]) (prep e))
           (set-E-labels! e (list (labelof (rac exps))))]
          [(E: (or (And exps) (Or exps)))
           (for ([e (in-list exps)]) (prep e))
           (set-E-labels! e (list (fresh-label e)))]
          [(E: (If test then els))
           (prep test)
           (prep then)
           (prep els)
           (set-E-labels! e (list (fresh-label e) (fresh-label #f) (fresh-label #f)))]
          [(E: (Set! x body))
           (note-variable! x)
           (prep body)
           (set-E-labels! e (list (fresh-label e)))]
          [(E: (Letcc x e1))
           (note-variable! x)
           (prep e1)
           (set-E-labels! e (list (fresh-label e)))]
          [_ (error 'prep "Bad ~a" e)])))
        (set-variables! '())
        (prepare tree '())
        (define v (list->vector (reverse labels)))
        (set-label->node! (lambda (l) (vector-ref v l)))
        (set-n-labels! (vector-length v))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract Evaluation.

;; Compute abstract values.
(define memo-propagate #f)
(define propagate-compare
  (lambda (a b)
    (and (= (labelof (car a)) (labelof (car b)))
         (equal? (cadr a) (cadr b))
         (andmap (lambda (c d)
                   (and (eq? (car c) (car d))
                        (equal? (cdr c) (cdr d))))
           (env->list (caddr a))
           (env->list (caddr b))))))
(define noisy-propagate
  (lambda (e k aenv)
    (printf "Propagate ~a ~a ~a~%" (labelof e) k (map (lambda (b) (list (pname (car b)) (cdr b))) (env->list aenv)))
    (propagate e k aenv)))

;; exp x context x env -> point
(define propagate
  (lambda (e k aenv)
    (define l (labelof e))
    (match e
      [(E: (Const c))
       (define p (index-result-map l k))
       (p+aval p
               (match c
                 [(? symbol?) (aval 'sym l)]
                 [#t          (aval 'true l)]
                 [#f          (aval 'false l)]
                 ['()         (aval 'nil l)]
                 [(? number?) (aval 'num l)]
                 [(? char?)   (aval 'char l)]
                 [(? string?) (aval 'str l)]
                 [(? void?)   (aval 'void l)]))
       p]
      [(E: (or (? Lam?) (? Vlam?)))
       (define p (index-result-map l k))
       (define frees (free-in-exp e))
       (define aenv* (aenv-restrict aenv frees))
       (p+aval p (aval 'closure l (make-closure-contour k) aenv*))
       p]
      [(E: (Var x))
       (cond [(Name-primitive? x)
              (define p (index-result-map l k))
              (p+aval p (aval 'prim l))
              p]
             [(Name-unbound? x)
              (define p (index-result-map l k))
              (p+aval p (aval 'unbound 0))
              p]
             [(and (Name-let-bound? x) (not (Name-mutated? x)))
              (define let-label (labelof (Name-binding x)))
              (define recursive? (recursive-var? e))
              (define component (or (Name-component x) (list x)))
              (var-split x aenv l k let-label recursive? component)]
             [else
              (result-map= l k (index-var-map x (aenv-lookup aenv x)))
              (index-result-map l k)])]
      [(E: (App e0 args))
       (let loop ([a* args])
         (if (pair? a*)
             (p->1 (propagate (car a*) k aenv)
                   (lambda () (loop (cdr a*))))
             ;; call e0 functions with args' labels
             (p-> (propagate e0 k aenv)
                  (make-ap-action
                   l
                   k
                   (make-ap-get-args args k (cdr (extra-labels e)))))))
       (index-result-map l k)]
      [(E: (or (Let b e2) (Letr b e2)))
       (define new-aenv
         (for/fold ([env aenv])
             ([cl (in-list b)]
              #:when (Define? cl))
           (aenv-extend env (Define-name cl) k)))
       (define (make-new-k eb)
         (make-context
          (let-binding-contour (context->contour k) (labelof eb))
          new-aenv))
       (let loop ([b b])
         (match b
           [(cons (Define x eb) rest)
            (when (Name-used-before-defined? x)
              (p+aval (index-var-map x k) (aval 'unspecified 0)))
            (let ([p (index-var-map x k)])
              (p->p (propagate eb (make-new-k eb) new-aenv) p)
              (p->1 p (lambda () (loop rest))))]
           [(cons (? E? eb) rest)
            (p->1 (propagate eb (make-new-k eb) new-aenv)
                  (lambda () (loop rest)))]
           [(cons _ rest)
            (loop rest)]
           ['()
            (propagate e2 k new-aenv)]
           [_ (error 'flow "Bad clause in let ~a" b)]))
       (index-result-map l k)]
      [(E: (Begin exps))
       (let eloop ([exps exps])
         (when (pair? exps)
           (p->1 (propagate (car exps) k aenv)
                 (lambda () (eloop (cdr exps))))))
       (index-result-map l k)]
      [(E: (If test then els))
       (match-let* ([tst (propagate test k aenv)]
                    [(list then-lbl else-lbl) (extra-labels e)]
                    [(cons then-env else-env)
                     (if If-split
                         (split-if test k aenv aenv then-lbl else-lbl)
                         (cons aenv aenv))]
                    [p (index-result-map l k)])
         (p-> tst
              (let ([first #t])
                (lambda (new)
                  (when (and first (except-in-avals? '(false) new))
                    (set! first #f)
                    (p->p (propagate then k then-env) p)))))
         (p-> tst
              (let ([first #t])
                (lambda (new)
                  (when (and first (in-avals? '(unspecified unbound false) new))
                    (set! first #f)
                    (p->p (propagate els k else-env) p)))))
         p)]
      [(E: (Set! x body))
       (let ([p1 (propagate body k aenv)])
         (unless (Name-unbound? x)
           (p->p p1 (index-var-map x (aenv-lookup aenv x)))))
       (let* ([p (index-result-map l k)])
         (p+aval p (aval 'void l))
         p)]
      [(E: (And exps))
       (let* ([p (index-result-map l k)])
         (if (null? exps)
             (p+aval p (aval 'true l))
             (let loop ([exps exps])
               (if (pair? (cdr exps))
                   (p-> (propagate (car exps) k aenv)
                        (let ([first #t])
                          (lambda (new)
                            (when (and first (except-in-avals? '(false) new))
                              (set! first #f)
                              (loop (cdr exps)))
                            (p+avals p (filter-avals '(false unspecified unbound) new)))))
                   (p->p (propagate (car exps) k aenv) p))))
         p)]
      [(E: (Or exps))
       (let* ([p (index-result-map l k)])
         (if (null? exps)
             (p+aval p (aval 'false l))
             (let loop ([exps exps])
               (if (pair? (cdr exps))
                   (p-> (propagate (car exps) k aenv)
                        (let ([first #t])
                          (lambda (new)
                            (when (and first (in-avals? '(false unspecified unbound) new))
                              (set! first #f)
                              (loop (cdr exps)))
                            (p+avals p (except-avals '(false) new)))))
                   (p->p (propagate (car exps) k aenv) p))))
         p)]
      [(E: (Letcc x e1))
       (let* ([p (index-result-map l k)]
              [aenv (aenv-extend aenv x k)])
         (p+aval (index-var-map x k) (aval 'cont l k))
         (p->p (propagate e1 k aenv) p)
         p)])))

;; Make an edge that filters based on type
(define typed-p->
  (lambda (type p1 p2)
    (p-> p1
         (lambda (new)
           (p+avals
             p2
             (intset-filter (lambda (v) (equal? (aval-type v) type)) new))))))

;; Build arg successor for type-based contours.
(define make-typed-arg-successor
  (lambda (contour-maps formals args current-contour eval-body)
    (lambda (from contour-map)
      (p-> from
           (lambda (new)
             (intset-for-each
               (lambda (v)
                 (define type (aval-type v))
                 (unless (assoc type (unbox contour-map))
                   ;; For a new type of arg, compute new contours,
                   ;; record them, evaluate function body in new
                   ;; contours, and add typed edges for all args
                   ;; and all appropriate types to formals.
                   (define arg-types
                     (for/list ([z (in-list contour-maps)])
                       (if (eq? z contour-map)
                           (list type)
                           (map car (unbox z)))))
                   (define new-contours
                     (make-type-based-contours
                      arg-types
                      current-contour))
                   (set-box! contour-map
                             (cons (cons type new-contours) (unbox contour-map)))
                   (for ([c (in-list new-contours)])
                     (eval-body c)
                     (for ([formal (in-list formals)]
                           [arg (in-list args)]
                           [types (in-list arg-types)])
                       (typed-p-> type arg (index-var-map formal c))))))
               new))))))

(define make-ap-action
  (lambda (l k get-args)
    (define p (index-result-map l k))
    (lambda (fns)
      (intset-for-each
       (lambda (new)
         (define l-closure (aval-label new))
         (case (aval-kind new)
           [(closure)
            (extend-call-map! l-closure l)
            (define aenv2 (aval-env new))
            (define c (call-site-contour l k (aval-contour new)))
            (define (action x arg* eval-body)
              (cond
               [(and Type (< (contour-length c) Type))
                (cond [(null? x) (eval-body c)]
                      [else
                       (define contour-maps (map (lambda (_) (box '())) x))
                       (define arg-successor
                         (make-typed-arg-successor
                          contour-maps
                          x
                          arg*
                          c
                          eval-body))
                       (for ([arg (in-list arg*)]
                             [contour (in-list contour-maps)])
                         (arg-successor arg contour))])]
               [else
                (for ([arg (in-list arg*)]
                      [contour (in-list x)])
                  (p->p arg (index-var-map contour c)))
                (eval-body c)]))
            (define node (label->node l-closure))
            (match node
              [(E: (Lam: x e2))
               (match (get-args (length x) #f #f)
                 [#f #f]
                 [(cons arg* _)
                  (define (eval-body c)
                    (define new-aenv
                      (aenv-extend* aenv2 x (map (lambda (_) c) x)))
                    (define new-context (make-context c aenv2))
                    (memo-propagate e2 new-context new-aenv)
                    (p->p (index-result-map (labelof e2) new-context) p))
                  (action x arg* eval-body)])]
              [(E: (Vlam: x rest e2))
               (match (get-args (length x) #f #t)
                 [#f #f]
                 [(cons arg* arg-rest)
                  (define (eval-body c)
                    (p->p arg-rest (index-var-map rest c))
                    (let* ([vars (cons rest x)]
                           [new-aenv (aenv-extend* aenv2 vars (map (lambda (_) c) vars))]
                           [new-context (make-context c aenv2)])
                      (memo-propagate e2 new-context new-aenv)
                      (p->p (index-result-map (labelof e2) new-context) p)))
                  (action x arg* eval-body)])])]
           [(unbound)
            (p+aval p (aval 'unbound 0))]
           [(cont)
            (extend-call-map! l-closure l)
            (let ([k2 (aval-contour new)])
              (match (label->node l-closure)
                [(and e2 (E: (? Letcc?)))
                 (match (get-args 1 #f #f)
                   [#f #f]
                   [`((,arg) . ,_)
                    (p->p arg (index-result-map (labelof e2) k2))])]))]
           [(prim)
            (extend-call-map! l-closure l)
            (match (label->node l-closure)
              [(and e2 (E: (Var x)))
               (for-each
                (lambda (arity)
                  (match (if (negative? arity)
                             (get-args (- (- arity) 1) #t #f)
                             (get-args arity #f #f))
                    [#f #f]
                    [`(,arg* . ,arg-rest)
                     (cond
                      [(eq? %internal-apply x)
                       (let* ([f (car arg*)]
                              [args-list (cadr arg*)]
                              [get-args (make-apply-get-args args-list)])
                         (p-> f (make-ap-action l k get-args)))]
                      [(or (eq? %vector x) (eq? %Qvector x))
                       (let* ([l-result (car (extra-labels e2))]
                              [p-result (index-result-map l-result k)])
                         (for-each
                          (lambda (arg) (p->p arg p-result))
                          arg*)
                         (when arg-rest
                           (p->p arg-rest p-result))
                         (when (zero? (length arg*))
                           (p+aval p (aval 'vec0 l-result)))
                         (p+aval p (aval 'vec l-result k p-result)))]
                      [(eq? %make-vector x)
                       (let* ([l-result (car (extra-labels e2))]
                              [p-result (index-result-map l-result k)])
                         (if (= 2 arity)
                             (p->p (cadr arg*) p-result)
                             (p+aval p-result (aval 'unspecified 0)))
                         (p+aval p (aval 'vec0 l-result))
                         (p+aval p (aval 'vec l-result k p-result)))]
                      [(memq x read-like-procedures)
                       (match (extra-labels e2)
                         [(list k l3 l4)
                          (p->p (memo-make-read-result k l3 l4) p)])]
                      [(eq? %Qlist x)
                       (let ([l3 (car (extra-labels e2))])
                         (p->p (memo-make-recursive-list l3 k arg*) p))]
                      [(eq? %Qmerge-list x)
                       (let* ([l-result (car (extra-labels e2))]
                              [lm (cadr (extra-labels e2))]
                              [pm (index-result-map lm k)])
                         (for-each
                          (lambda (arg) (p->p arg pm))
                          arg*)
                         (p->p (memo-make-recursive-list l-result k (list pm)) p))]
                      [else
                       (match (Name-primop x)
                         [(Constructor tag)
                          (let ([l3 (car (extra-labels e2))])
                            (p+aval p
                                    (apply aval
                                           tag
                                           l ;;; TEMP l3 -> l
                                           k
                                           arg*)))]
                         [(Selector tag idx)
                          (p-> (car arg*)
                               (lambda (new)
                                 (intset-for-each
                                  (lambda (v)
                                    (when (eq? tag (aval-kind v))
                                      (p->p (list-ref (aval-fields v) idx)
                                            p)))
                                  new)))]
                         [(Mutator tag idx val)
                          (let ([l3 (car (extra-labels e2))])
                            (p-> (car arg*)
                                 (lambda (new)
                                   (intset-for-each
                                    (lambda (v)
                                      (when (eq? tag (aval-kind v))
                                        (p->p (list-ref arg* val)
                                              (list-ref (aval-fields v) idx))))
                                    new)))
                            (p+aval p (aval 'void l3)))]
                         [(Predicate tags)
                          (let ([l3 (car (extra-labels e2))])
                            (p-> (car arg*)
                                 (lambda (new)
                                   (intset-for-each
                                    (lambda (v)
                                      (when (memq (aval-kind v)
                                                  `(unspecified unbound ,@tags))
                                        (p+aval p (aval 'true l3)))
                                      (unless (memq (aval-kind v) tags)
                                        (p+aval p (aval 'false l3))))
                                    new))))]
                         [_
                          (let ([l3 (car (extra-labels e2))])
                            (p+avals
                             p
                             (list->avals
                              (map (lambda (c) (aval c l)) ;;; TEMP l3 -> l
                                   (Primitive-result-type (Name-binder x))))))])])]))
                (Primitive-arity (Name-binder x)))])]))
       fns))))

;; Build a get-args closure for an ordinary application.  A get-args
;; closure takes three args: n, or-more?, and rest?.  n is the
;; minimum number of args required.  or-more? is true if an arbitrary
;; number of args can be accepted.  rest? is true if an arbitrary
;; number of args can be accepted and they are to be returned as
;; a list (for a Vlam).  Only one of or-more? and rest? may be true.
;; A get-args closure returns
;;       #f if the args request cannot be satisfied;
;;       a pair of (list of length n) and #f if both or-more? and rest? are false
;;       a pair of (list of length >= n) and a rest point if or-more? is true
;;       a pair of (list of length n) and a rest point if rest? is true.
(define memo-make-ap-get-args #f) ; not used
(define make-ap-get-args
  (lambda (args k labels)
    (let ([nargs (length args)]
          [largs (map labelof args)])
      (lambda (n or-more? rest?)
        (if (cond (or-more? (< nargs n))
                  (rest? (< nargs n))
                  (else (not (= n nargs))))
            #f
            (let ([points (map (lambda (l) (index-result-map l k))
                               (if or-more? largs (sublist largs n)))])
              (cons points
                    (cond [rest? (make-varargs-list
                                   (list-tail largs n)
                                   k
                                   (list-tail labels n))]
                          [or-more? (if (null? points) #f (car points))]
                          [else #f]))))))))

;; This function assumes that p includes a single recursive cons
;; whose cdr refers to a program point equivalent to p.
;; This program point is expected to be the result of list-copy.
(define make-apply-get-args
  (lambda (p)
    (let* ([pairs (intset->list (filter-avals '(cons) (point-elements p)))]
           [v (if (= 1 (length pairs))
                  (car pairs)
                  (error 'internal-apply "args not correctly formed"))]
           [arg-k (aval-contour v)]
           [arg-car (car (aval-fields v))])
      (lambda (n or-more? rest?)
        (cons (iota n arg-car)
              (cond (rest? p)
                    (or-more? arg-car)
                    (else #f)))))))

(define make-varargs-list
  (lambda (largs k labels)
    (let ([p (index-result-map (car labels) k)])
      (if (null? largs)
          (p+aval p (aval 'nil (car labels)))
          (begin
            (p+aval p (aval 'cons (car labels) k
                            (index-result-map (car largs) k)
                            (index-result-map (cadr labels) k)))
            (make-varargs-list (cdr largs) k (cdr labels))))
      p)))

(define memo-make-read-result #f)
(define make-read-result
  (lambda (k l1 l2)
    (define p (index-result-map l1 k))
    (define p2 (index-result-map l2 k))
    (define vals (list
                  (aval 'nil l1)
                  (aval 'sym l1)
                  (aval 'true l1)
                  (aval 'false l1)
                  (aval 'num l1)
                  (aval 'char l1)
                  (aval 'str l1)
                  (aval 'cons l1 k p2 p2)
                  (aval 'vec0 l1)
                  (aval 'vec l1 k p2)))
    (p+avals p2 (list->avals vals))
    (p+avals p (list->avals (cons (aval 'eof l1) vals)))
    p))

(define memo-make-recursive-list #f)
(define make-recursive-list
  (lambda (l k elts)
    (let* ([p (index-result-map l k)]
           [vals (cons (aval 'nil l)
                       (map (lambda (elt) (aval 'cons l k elt p))
                            elts))])
      (p+avals p (list->avals vals))
      p)))

;; Split variables in the test of an if-expression if we can
;; determine that they have a certain shape in the then and/or else branches.
(define split-if
  (lambda (exp k then-env else-env then-label else-label)
    (letrec ([split-variable
              (lambda (sense tags x-label x)
                (let* ([xpoint (index-result-map x-label k)]
                       [then-contour (if-contour
                                       (aenv-lookup then-env x)
                                       then-label)]
                       [x-then-point (index-var-map x then-contour)]
                       [then-env (aenv-extend then-env x then-contour)]
                       [else-contour (if-contour
                                       (aenv-lookup else-env x)
                                       else-label)]
                       [x-else-point (index-var-map x else-contour)]
                       [else-env (aenv-extend else-env x else-contour)]
                       [f (case sense
                            [(both)
                             (lambda (new)
                               (let ([filtered (filter-avals tags new)])
                                 (p+avals x-then-point filtered)
                                 (p+avals x-else-point filtered)))]
                            [(#t)
                             (lambda (new)
                               (p+avals x-then-point (filter-avals tags new))
                               (p+avals x-else-point (except-avals tags new)))]
                            [(#f)
                             (lambda (new)
                               (p+avals x-then-point (except-avals tags new))
                               (p+avals x-else-point (filter-avals tags new)))])])
                  (p-> xpoint f)
                  (cons then-env else-env)))]
             [find-var-to-split
              (lambda (exp then-env else-env)
                (match exp
                  [(E: (App (E: (Var p-or-s)) (list (and (E: (Var x)) expr))))
                   (define xl (labelof expr))
                   (cond [(or (Name-mutated? x)
                              (Name-primitive? x)
                              (Name-unbound? x)
                              (not (Name-primitive? p-or-s))
                              (and (not (Predicate? (Name-primop p-or-s)))
                                   (not (Selector? (Name-primop p-or-s)))))
                          (cons then-env else-env)]
                         [(Predicate? (Name-primop p-or-s))
                          (split-variable #t (Predicate-tag (Name-primop p-or-s)) xl x)]
                         [else ; Selector
                          (split-variable 'both (list (Selector-tag (Name-primop p-or-s))) xl x)])]
                  [(E: (Var x))
                   (cond [(or (Name-mutated? x) (Name-unbound? x))
                          (cons then-env else-env)]
                         [else
                          (split-variable #f (list 'false) (labelof exp) x)])]
                  [(E: (App (E: (Var p-or-s)) (list arg)))
                   (if (and (Name-primitive? p-or-s)
                            (or (Predicate? (Name-primop p-or-s))
                                (Selector? (Name-primop p-or-s))))
                         (find-var-to-split arg then-env else-env)
                         (cons then-env else-env))]
                  [(E: (And (list exp)))
                   (find-var-to-split exp then-env else-env)]
                  [(E: (And exps))
                   (let loop ([exps exps] [then-env then-env])
                     (if (null? exps)
                         (cons then-env else-env)
                         (match-let ([`(,then-env . ,_)
                                      (find-var-to-split (car exps) then-env else-env)])
                           (loop (cdr exps) then-env))))]
                  [_ (cons then-env else-env)]))])
      (find-var-to-split exp then-env else-env))))

(define warn-unused-vars
  (lambda ()
    (for-each
      (lambda (x)
        (when (intset-empty? (values-at-var x))
          (printf "; Note: ~a never gets a value~%" (pname* x))))
      variables)))

(define not-called?
  (lambda (v)
    (null? (index-call-map (aval-label v)))))

(define warn-uncalled
  (lambda ()
    (match tree
      [(E: (Letr b _))
       (for-each
         (match-lambda
           [(Define x e)
            (when (intset-exists?
                    not-called?
                    (filter-avals '(closure prim) (values-at-label (labelof e))))
              (printf "; Note: ~a is never called~%" (pname* x)))]
           [_ #f])
         b)])))
