#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simplify by doing simple syntactic reductions.

(provide simplify)

;; First walk over an expression (the program) reducing simple
;; redexes and not going inside lambdas.  Then repeat this
;; inside any lambdas remaining.  Since lambdas are never
;; duplicated, this algorithm never duplicates work.

;; This implementation assumes that no pieces of the tree are
;; shared, and preserves this invariant.

;; As simplifying may eliminate free variables, it may become
;; possible to simplify further after a round of simplification
;; has been completed.  Hence we repeat the simplification process
;; a few times.

(define simplify-rounds 20)

(define simplify
  (letrec
    ([progress #f]
     [simp
      (lambda (e)
        (match e
          [($ E ($ App fun args))
           (simp fun)
           (for-each simp args)
           (match (cons fun args)
             [(($ E ($ Lam x e1)) . _)
              (when (= (length x) (length args))
                (set! progress #t)
                (set-E-exp! e
                  (E-exp
		   (make-E (make-Let
			    (map make-Define x args)
			    e1))))
                (simp e))]
             [(($ E ($ Vlam x rest e1)) . _)
              (when (<= (length x) (length args))
                (set! progress #t)
                (set-E-exp! e
                  (E-exp
		   (let* ((build-rest 
			   (lambda (args)
			     (list (make-Define 
				    rest
				    (foldr
				     (lambda (arg exp)
				       (make-E (make-App
						(make-E (make-Var %cons))
						(list arg exp))))
				     (make-E (make-Const '()))
				     args)))))
			  (bindings 
			   (if (null? x)
			       (build-rest args)
			       (let loop [(formals x)
					    (args args)
					    (bindings (list))]
				      (if (null? formals)
					  (append bindings
						  (build-rest args))
					  (loop (cdr formals)
						(cdr args)
						(cons (make-Define
						       (car formals)
						       (car args))
						      bindings)))))))
		     (make-E (make-Let bindings e1)))))
		(simp e))]
             [(($ E ($ Var (? simple-primitive? x))) . (($ E (? Const? c)) ...))
              (when (applies-to?
                      (Primitive-arity (Name-binder x))
                      (Primitive-arg-types (Name-binder x))
                      (map type-of-const c))
                (set! progress #t)
                (set-E-exp! e (make-Const (eval `(,(pname x) ,@(map pexpr args))))))]
             [(($ E ($ Var (? closure-ref?))) . (($ E ($ App ($ E ($ Var (? make-closure?))) exps)) ($ E ($ Const n))))
              (set! progress #t)
              (set-E-exp! e (E-exp (list-ref exps n)))]
             [_ (void)])]
          [($ Define x body)
           (simp body)]
          [($ E ($ And exps))
           (for-each simp exps)
           (match exps
             [(or (a) ((and a ($ E ($ Const #f))) . _))
              (set! progress #t)
              (set-E-exp! e (E-exp a))]
             [_ (void)])]
          [($ E ($ Or exps))
           (for-each simp exps)
           (match exps
             [(or (a) ((and a ($ E ($ Const (not #f)))) . _))
              (set! progress #t)
              (set-E-exp! e (E-exp a))]
             [_ (void)])]
          [($ E ($ Begin exps))
           (for-each simp exps)
           (let loop ([exps exps] [new '()])
             (match exps
               [(a)
                (if (null? new)
                    (begin
                      (set! progress #t)
                      (set-E-exp! e (E-exp a)))
                    (set-E-exp! e (make-Begin (reverse (cons a new)))))]
               [(($ E ($ Var (? Name-primitive?))) . rest)
                (set! progress #t)
                (loop rest new)]
               [(e1 . rest)
                (loop rest (if (eq? (purity e1) 'W)
                               (cons e1 new)
                               (begin
                                 (set! progress #t)
                                 new)))]))]
          [($ E ($ Let b body))
           (for-each simp b)
           (let loop ([b b] [env empty-env] [new-b '()])
             (match b
               ['()
		(unless (empty-env? env)
		  (set! progress #t)
	          (substitute! body env))
                (simp body)
                (if (null? new-b)
                    (begin
                      (set! progress #t)
                      (set-E-exp! e (E-exp body)))
                    (set-E-exp! e (make-Let (reverse new-b) body)))]
               [((and d ($ Define x e1)) . rest)
                (if (and (not (Name-mutated? x))
                         (match (purity e1)
                           [#f (or (small? e1) (<= (num-occurs x body) 1))]
                           ['A (<= (num-occurs x body) 1)]
                           ['R (= (num-occurs x body) 0)]
                           ['W #f]))
                    (loop rest (extend-env env x e1) new-b)
                    (loop rest env (cons d new-b)))]))]
          [($ E ($ Letr b body))
           (for-each simp b)
           (simp body)
           (let ([b (filter
                      (let ([fv-body (free-in-exp body)])
                        (lambda (d)
                          (if (match d
                                [($ Define x e1)
                                 (or (memq x fv-body)
                                     (eq? 'W (purity e1))
                                     (ormap
                                       (lambda (d) (memq x (free-in-exp d)))
                                       (setdiff b (set d))))]
                                [(? E?)
                                 (eq? 'W (purity d))]
                                [_ #t])
                              #t
                              (begin
                                (set! progress #t)
                                #f))))
                      b)])
             (if (null? b)
                 (begin
                   (set! progress #t)
                   (set-E-exp! e (E-exp body)))
                 (set-E-exp! e (make-Letr b body))))]
          [($ E ($ If e1 e2 e3))
           (simp e1)
           (simp e2)
           (simp e3)
           (match e1
             [($ E ($ Const #f))
              (set! progress #t)
              (set-E-exp! e (E-exp e3))]
             [($ E ($ Const _))
              (set! progress #t)
              (set-E-exp! e (E-exp e2))]
             [_ (void)])]
          [($ E ($ Letcc _ exp))
           (simp exp)]
          [($ E ($ Set! _ exp))
           (simp exp)]
          [_ (void)]))]
     [simp-inside
      (lambda (e)
        (match e
          [($ E ($ Lam _ body))
           ; Because we operate imperatively, remove free variable caching
           ; so next round of simplification will see correct free vars.
           (set-Lam-free! (E-exp e) #f)
           (simp body)
           (simp-inside body)]
          [($ E ($ Vlam _ _ body))
           ; See comment above.
           (set-Vlam-free! (E-exp e) #f)
           (simp body)
           (simp-inside body)]
          [($ Define _ body)
           (simp-inside body)]
          [($ E (or ($ And exps) ($ Or exps) ($ Begin exps)))
           (for-each simp-inside exps)]
          [($ E ($ App fun args))
           (simp-inside fun)
           (for-each simp-inside args)]
          [($ E (or ($ Let b e2) ($ Letr b e2)))
           (for-each simp-inside b)
           (simp-inside e2)]
          [($ E ($ If e1 e2 e3))
           (simp-inside e1)
           (simp-inside e2)
           (simp-inside e3)]
          [($ E ($ Letcc _ exp))
           (simp-inside exp)]
          [($ E ($ Set! _ exp))
           (simp-inside exp)]
          [_ (void)]))])
    (lambda ()
      (let loop ([n 1])
        (unless (> n simplify-rounds)
          (printf "Simplify round ~a ...~%" n)
          (set! progress #f)
          (simp tree)
          (simp-inside tree)
          (when progress (loop (+ n 1))))))))

(define simple-primitive?
  (lambda (x)
    (and (Name-primitive? x) (Primitive-can-be-simplified? (Name-binder x)))))

(define make-closure?
  (lambda (x)
    (and (Name-primitive? x) (eq? (Name-name x) 'make-closure))))

(define closure-ref?
  (lambda (x)
    (and (Name-primitive? x) (eq? (Name-name x) 'closure-ref))))

(define type-of-const
  (match-lambda
    [($ Const #f) '(false)]
    [($ Const #t) '(true)]
    [($ Const '()) '(nil)]
    [($ Const (? symbol?)) '(sym)]
    [($ Const (? number?)) '(num)]
    [($ Const (? char?)) '(char)]
    [($ Const (? string?)) '(str)]
    [($ Const (? void?)) '(void)]))

(define substitute!
  (lambda (e env)
    (unless (empty-env? env)
      (let substitute ([e e] [env env])
        (match e
          [($ E ($ Var x))
           (match (lookup? env x)
             [#f (void)]
             [v (set-E-exp! e (E-exp (copy-exp v)))])]
          [($ Define x body)
           (substitute body env)]
          [($ E ($ Lam x e1))
           (set-Lam-free! (E-exp e) #f)
           (substitute e1 (filter-env (lambda (y) (not (memq y x))) env))]
          [($ E ($ Vlam x rest e1))
           (set-Vlam-free! (E-exp e) #f)
           (substitute e1 (filter-env (lambda (y) (not (memq y (cons rest x)))) env))]
          [($ E (or ($ And exps) ($ Or exps) ($ Begin exps)))
           (for-each (lambda (x) (substitute x env)) exps)]
          [($ E ($ App e1 args))
           (substitute e1 env)
           (for-each (lambda (x) (substitute x env)) args)]
          [($ E ($ Let b e2))
           (for-each (lambda (x) (substitute x env)) b)
           (let* ([x (map Define-name b)]
                  [env (filter-env (lambda (y) (not (memq y x))) env)])
             (substitute e2 env))]
          [($ E ($ Letr b e2))
           (let* ([x (map Define-name b)]
                  [env (filter-env (lambda (y) (not (memq y x))) env)])
             (for-each (lambda (x) (substitute x env)) b)
             (substitute e2 env))]
          [($ E ($ If e1 e2 e3))
           (substitute e1 env)
           (substitute e2 env)
           (substitute e3 env)]
          [($ E ($ Letcc x exp))
           (substitute exp (filter-env (lambda (y) (not (eq? y x))) env))]
          [($ E ($ Set! _ exp))
           (substitute exp env)]
          [_ (void)])))))

(define num-occurs
  (lambda (x e)
    (let num-occurs ([e e])
      (match e
        [($ E ($ Var y))
         (if (eq? y x) 1 0)]
        [($ E (? Const?))
         0]
        [($ Define x body)
         (num-occurs body)]
        [($ E ($ Lam y e1))
         (if (memq x y)
             0
             (num-occurs e1))]
        [($ E ($ Vlam y rest e1))
         (if (or (memq x y) (eq? x rest))
             0
             (num-occurs e1))]
        [($ E (or ($ And exps) ($ Or exps) ($ Begin exps)))
         (foldl + 0 (map num-occurs exps))]
        [($ E ($ App e1 args))
         (foldl + (num-occurs e1) (map num-occurs args))]
        [($ E ($ Let b e2))
         (foldl
           +
           (if (memq x (definition-names b))
               0
               (num-occurs e2))
           (map num-occurs b))]
        [($ E ($ Letr b e2))
         (if (memq x (definition-names b))
             0
             (foldl + (num-occurs e2) (map num-occurs b)))]
        [($ E ($ If e1 e2 e3))
         (+ (num-occurs e1) (num-occurs e2) (num-occurs e3))]
        [($ E ($ Letcc y exp))
         (if (eq? x y)
             0
             (num-occurs exp))]
        [($ E ($ Set! y exp))
         (+ (if (eq? y x) 1 0) (num-occurs exp))]))))

(define purity<=
  (lambda (x y)
    (or (or (eq? x y))
        (not x)
        (and (eq? x 'A) (or (eq? y 'R) (eq? y 'W)))
        (and (eq? x 'R) (eq? y 'W)))))

(define purity
  (let ([combine (lambda (x y)
                   (if (purity<= x y)
                       y
                       x))])
    (match-lambda
      [($ Define x body)
       (purity body)]
      [($ Var x)
       (if (Name-mutated? x)
           'R
           #f)]
      [($ E (or (? Lam?) (? Vlam?) (? Const?)))
       #f]
      [($ E (or ($ And exps) ($ Or exps) ($ Begin exps)))
       (foldl combine #f (map purity exps))]
      [($ E ($ App ($ E ($ Var (? Name-primitive? f))) args))
           (combine
             (Primitive-purity (Name-binder f))
             (foldl combine #f (map purity args)))]
       ;; At present we cannot assume that primitives are applied correctly
;       (if (applies-to?
;             (Primitive-arity (Name-binder f))
;             (Primitive-arg-types (Name-binder f))
;             (map (lambda (a) '(_)) args))
;           (combine
;             (Primitive-purity (Name-binder f))
;             (foldl combine #f (map purity args)))
;           'W)]
      [($ E (? App?))
       'W]
      [($ E (or ($ Let b e2) ($ Letr b e2)))
       (combine
         (foldl combine #f (map purity b))
         (purity e2))]
      [($ E ($ If e1 e2 e3))
       (combine
         (combine (purity e1) (purity e2))
         (purity e3))]
      [($ E (or (? Set!?) (? Letcc?)))
       'W]
      [_ #f])))

(define small?
  (match-lambda
    [($ E (or (? Const?) (? Var?))) #t]
    [_ #f]))

(define (copy-exp e)
  (match e
   [($ E ($ Const c))
    (like-E (make-Const c) e)]
   [($ E ($ Var x))
    (like-E (make-Var x) e)]
   [($ Define x body)
    (make-Define x (copy-exp body))]
   [($ E ($ Lam y e1))
    (like-E (make-Lam y (copy-exp e1)) e)]
   [($ E ($ Vlam y rest e1))
    (like-E (make-Vlam y rest (copy-exp e1)) e)]
   [($ E ($ And exps))
    (like-E (make-And (map copy-exp exps)) e)]
   [($ E ($ Or exps))
    (like-E (make-Or (map copy-exp exps)) e)]
   [($ E ($ Begin exps))
    (like-E (make-Begin (map copy-exp exps)) e)]
   [($ E ($ App e1 args))
    (like-E (make-App (copy-exp e1) (map copy-exp args)) e)]
   [($ E ($ Let b e2))
    (like-E (make-Let (map copy-exp b) (copy-exp e2)) e)]
   [($ E ($ Letr b e2))
    (like-E (make-Letr (map copy-exp b) (copy-exp e2)) e)]
   [($ E ($ If e1 e2 e3))
    (like-E (make-If (copy-exp e1) (copy-exp e2) (copy-exp e3)) e)]
   [($ E ($ Letcc y exp))
    (like-E (make-Letcc y (copy-exp exp)) e)]
   [($ E ($ Set! y exp))
    (like-E (make-Set! y (copy-exp exp)) e)]))

(define alpha-exp
  (let ([count (generate-counter 0)])
    (match-lambda
      [($ E ($ Const c))
       (make-E (make-Const c))]
      [($ E ($ Var x))
       (set-Name-name! x (string->symbol (format "x~a" (count))))
       (make-E (make-Var x))]
      [($ Define x body)
       (make-Define x (alpha-exp body))]
      [($ E ($ Lam y e1))
       (make-E (make-Lam y (alpha-exp e1)))]
      [($ E ($ Vlam y rest e1))
       (make-E (make-Vlam y rest (alpha-exp e1)))]
      [($ E ($ And exps))
       (make-E (make-And (map alpha-exp exps)))]
      [($ E ($ Or exps))
       (make-E (make-Or (map alpha-exp exps)))]
      [($ E ($ Begin exps))
       (make-E (make-Begin (map alpha-exp exps)))]
      [($ E ($ App e1 args))
       (make-E (make-App (alpha-exp e1) (map alpha-exp args)))]
      [($ E ($ Let b e2))
       (make-E (make-Let (map alpha-exp b) (alpha-exp e2)))]
      [($ E ($ Letr b e2))
       (make-E (make-Letr (map alpha-exp b) (alpha-exp e2)))]
      [($ E ($ If e1 e2 e3))
       (make-E (make-If (alpha-exp e1) (alpha-exp e2) (alpha-exp e3)))]
      [($ E ($ Letcc y exp))
       (make-E (make-Letcc y (alpha-exp y)))]
      [($ E ($ Set! y exp))
       (make-E (make-Set! y (alpha-exp exp)))])))


;                    (foldr
;                      (lambda (binding exp) (make-E (make-Let (list binding) exp)))
;                      e1
;                      (map make-Define x args))))
