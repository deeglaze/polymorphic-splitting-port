 #lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Print an expression or definition.

(require "library.rkt"
         "env.rkt"
         "r4rsprim.rkt"
         "data.rkt"
         "free.rkt"
         "prim.rkt"
         "mutrec.rkt")
(provide pexprs pexprs-renamed pexprs-with-labels
         pexprs-with-checks
         pexprs-with-no-checks pexprs-with-all-checks
         pexpr pname
         pfn)

;; pexprs - print a list of expressions without checks, renaming, or labels
;; pexprs-with-checks - print expressions with run-time checks and renaming R4RS primitives
;; pexprs-with-labels - print expressions with labels and renaming R4RS primitives
;; pexprs-with-no-checks - print expressions with renmaming
;; pexprs-with-all-checks - print expressions with all possible checks, and renaming
;;
;; pname - print a name
;; pname* - print a name with context information
;; pfn - print the name of a closure

;; action gets called with keyword, expr where keyword is
;;  symbol   - for Var
;;  '()      - for App
;;  (symbol) - for other cases
(define unparse
  (lambda (e pname action env)
    (letrec
      ([rename (lambda (env x) (or (lookup? env x) (pname x)))]
       [pexpr
        (lambda (e env)
          (match e
            [(Define x body)
             (action e `(define ,(rename env x) ,(pexpr body env)))]
            [(Defstruct tag con pred sels muts)
             (action e `(defstruct
                          ,tag
                          ,(rename env con)
                          ,(rename env pred)
                          ,@(map (lambda (sel mut)
                                   (if mut
                                       `(,(rename env sel) ,(rename env mut))
                                       (rename env sel)))
                                 sels
                                 muts)))]
            [(Defmacro m)
             (action e m)]
            [(E: (Var x))
             (if (eq? x %internal-apply)
                 `(|#special| internal-apply)
                 (action e (rename env x)))]
            [(E: (Lam: x e1))
             (let* ([names (rename-avoiding x e pname)]
                    [new-env (extend-env* env x names)])
               (action e `(lambda ,names ,(pexpr e1 new-env))))]
            [(E: (Vlam: x rest e1))
             (let* ([names (rename-avoiding (cons rest x) e pname)]
                    [new-env (extend-env* env (cons rest x) names)])
               (action e `(lambda
                            ,(append (cdr names) (car names))
                            ,(pexpr e1 new-env))))]
            [(E: (And exps))
             (action e `(and ,@(map (lambda (e) (pexpr e env)) exps)))]
            [(E: (Or exps))
             (action e `(or ,@(map (lambda (e) (pexpr e env)) exps)))]
            [(E: (Begin exps))
             (action e `(begin ,@(map (lambda (e) (pexpr e env)) exps)))]
            [(E: (Const x))
             (action e (cond [(symbol? x) `(quote ,x)]
                             [(eq? (void) x) '(void)]
                             [(null? x) '(quote ())]
                             [else x]))]
            [(E: (App fun args))
	     (action e (map (lambda (e) (pexpr e env)) (cons fun args)))]
;	     (match fun
;		    [(E: (Lam: names body))
;		     (let ([transform (make-E (Let
;					       (map (lambda (a b)
;						      (Define a b))
;						    names
;						    args)
;					       body))])
;		       (pexpr transform env))]
;		    [else (action e (map (lambda (e) (pexpr e env)) (cons fun args)))])]
            [(E: (Let (list b1) (and e2 (E: (Let (list _) _)))))
             (let* ([x (Define-name b1)]
                    [name (car (rename-avoiding (list x) e pname))]
                    [new-env (extend-env env x name)]
                    [pb1 `(,name ,(pexpr (Define-exp b1) env))])
               (match-let ([(list-rest _ bindings body) (pexpr e2 new-env)])
                 (action e `(let* (,pb1 ,@bindings) ,@body))))]
            [(E: (Let b e2))
             (let* ([x (map Define-name b)]
                    [new-env (extend-env* env x (rename-avoiding x e pname))])
               (let ([pb (mapLR
                           (match-lambda
                             [(Define x e1) `(,(rename new-env x) ,(pexpr e1 env))])
                           b)])
                 (action e `(let ,pb ,(pexpr e2 new-env)))))]
	    [(E: (Clet names bindings body))
	     (pexpr (make-E (Let bindings body)) env)]
            [(E: (Letr b e2))
             (let* ([x (definition-names b)]
                    [new-env (extend-env* env x (rename-avoiding x e pname))])
               (let* ([non-defs (filter (lambda (x) (not (Define? x))) b)]
                      [pb (mapLR
                            (match-lambda
                              [(Define x e1) `(,(rename new-env x) ,(pexpr e1 new-env))])
                            (filter Define? b))]
                      [p2 (pexpr e2 new-env)]
                      [body (if (null? pb) p2 (action e `(letrec ,pb ,p2)))])
                 (if (null? non-defs)
                     body
                     `(let () ,@(mapLR (lambda (e) (pexpr e new-env)) non-defs) ,body))))]
            [(E: (If e1 e2 e3))
             (let* ([p1 (pexpr e1 env)]
                    [p2 (pexpr e2 env)]
                    [p3 (pexpr e3 env)])
               (action e `(if ,p1 ,p2 ,p3)))]
            [(E: (Letcc x e1))
             (let* ([name (car (rename-avoiding (list x) e pname))]
                    [new-env (extend-env env x name)])
               (action e `(lambda ,name ,(pexpr e1 new-env))))]
            [(E: (Set! x exp))
             (action e `(set! ,(rename env x) ,(pexpr exp env)))]
            [err (error 'pexpr "Unknown expr: ~a" err)]))])
      (pexpr e env))))

(define unparse*
  (lambda (e pname action)
    (match e
      [(E: (Letr b e2))
       (let* ([x (definition-names b)]
              [new-env (extend-env* empty-env x (rename-avoiding x e pname))])
         (mapLR (lambda (e) (unparse e pname action new-env)) b))]
      [(E: (Const (? void?))) '()])))

(define pexpr
  (lambda (e)
    (unparse e pname (compact-quote (lambda (e p) p)) empty-env)))

(define rename-avoiding
  (lambda (names e pname)
    (let ([new-name
           (lambda (name avoid)
             (let loop ([n 1])
               (let ([new (symbol-append name '@ n)])
                 (if (memq new avoid)
                     (loop (+ 1 n))
                     new))))]
          [free (free-names e)])
      (let loop ([names names]
                   [avoid (append
                            (map pname (setdiff free names))
                            '(define
                               defstruct
                               defmacro
                               and
                               begin
                               if
                               lambda
                               let
                               let*
                               letrec
                               or
                               delay
                               set!
                               letcc))])
        (if (null? names)
            '()
            (let* ([name (car names)]
                   [printed (pname name)]
                   [fresh (if (memq printed avoid)
                              (new-name printed avoid)
                              printed)])
              (cons fresh (loop (cdr names) (cons fresh avoid)))))))))

(define compact-quote
  (let ([%Qlist? (lambda (x) (eq? x %Qlist))]
        [%Qcons? (lambda (x) (eq? x %Qcons))]
        [%Qbox? (lambda (x) (eq? x %Qbox))]
        [%Qvector? (lambda (x) (eq? x %Qvector))]
        [%Qmerge-list? (lambda (x) (eq? x %Qmerge-list))]
        [unkwote (match-lambda
                   [`(quote ,x) x]
                   [(? boolean? x) x]
                   [(? number? x) x]
                   [(? char? x) x]
                   [(? string? x) x]
                   [(? null? x) x]
                   [(? box? x) x]
                   [(? vector? x) x])])
    (lambda (continue)
      (lambda (e p)
        (match e
          [(E: (App (E: (Var (? %Qlist?))) _))
           `(quote ,(map unkwote (cdr p)))]
          [(E: (App (E: (Var (? %Qmerge-list?))) _))
           `(quote ,(map unkwote (cdr p)))]
          [(E: (App (E: (Var (? %Qcons?))) _))
           (let* ([a (unkwote (cadr p))]
                  [d (unkwote (caddr p))])
             `(quote ,(cons a d)))]
          [(E: (App (E: (Var (? %Qbox?))) (list b)))
           (box (unkwote (cadr p)))]
          [(E: (App (E: (Var (? %Qvector?))) args))
           (list->vector (map unkwote (cdr p)))]
          [_ (continue e p)])))))

(define pexprs
  (lambda (e)
    (unparse* e pname (compact-quote (lambda (e p) p)))))

(define pexprs-renamed
  (lambda (e)
    (unparse* e pname-rename (compact-quote (lambda (e p) p)))))

(define pexprs-with-labels
  (lambda (e)
    (unparse*
      e
      pname
      (lambda (e p)
        (let ([labelit (lambda (it e)
                         (if (labeled? e)
                             (symbol-append it '^ (labelof e))
                             it))]
              [any-extra-labels (lambda (e)
                                  (if (labeled? e)
                                      (list (extra-labels e))
                                      '()))])
          (match e
            [(E: (Var x))
             (cond [(Name-primitive? x)
                    `(,(labelit 'PRIM e) ,@(any-extra-labels e) ,p)]
                   [(Name-let-bound? x)
                    `(,(labelit 'PVAR e) ,p)]
                   [else
                    `(,(labelit 'VAR e) ,p)])]
            [(E: (? App?))
             `(,(labelit 'AP e) ,@(any-extra-labels e) ,@p)]
            [(E: (? If?))
             `(,(labelit 'if e) ,@(any-extra-labels e) ,@(cdr p))]
            [(E: (? Const?))
             `(,(labelit 'CONST e) ,p)]
            [(? E?)
             (match p
               [`(,(? symbol? s) ,args ...) `(,(labelit s e) ,@args)])]
            [_ p]))))))

(define pexprs-with-checks
  (lambda (e)
    (let* ([pname pname-rename]
           [check-counter (generate-counter 0)]
           [defs (unparse*
                   e
                   pname
                   (compact-quote
                     (lambda (e p)
                       (match e
                         [(E: (Var x))
                          (if (and (Name-primitive? x) (check-needed? (labelof e)))
                              `(,(symbol-append 'CHECK- p) ,(check-counter))
                              p)]
                         [(E: (or (? Lam?) (? Vlam?)))
                          (if (check-needed? (labelof e))
                              `(CHECK-lambda (,(check-counter)) ,@(cdr p))
                              p)]
                         [(E: (? App?))
                          (if (check-needed? (labelof e))
                              `(CHECK-ap (,(check-counter)) ,@p)
                              p)]
                         [(E: (? Letcc?))
                          (if (check-needed? (labelof e))
                              `(CHECK-letcc (,(check-counter)) ,@(cdr p))
                              p)]
                         [(Defstruct tag con pred sels muts)
                          `(CHECK-defstruct ,@(cdr p))]
                         [_ p]))))])
      (cons defs (check-counter)))))

(define pexprs-with-no-checks
  (lambda (e)
    (unparse* e pname-rename (compact-quote (lambda (e p) p)))))

(define pexprs-with-all-checks
  (lambda (e)
    (let* ([pname pname-rename]
           [check-counter (generate-counter 0)]
           [defs (unparse*
                   e
                   pname
                   (compact-quote
                     (lambda (e p)
                       (match e
                         [(E: (Var x))
                          (if (and (Name-primitive? x) (not (eq? x %internal-apply)))
                              `(,(symbol-append 'CHECK- p) ,(check-counter))
                              p)]
                         [(E: (or (? Lam?) (? Vlam?)))
                          `(CHECK-lambda (,(check-counter)) ,@(cdr p))]
                         [(E: (App (E: (Var (? Name-primitive?))) _))
                          p]
                         [(E: (? App?))
                          `(CHECK-ap (,(check-counter)) ,@p)]
                         [(Defstruct tag con pred sels muts)
                          `(CHECK-defstruct ,@(cdr p))]
                         [_ p]))))])
      (cons defs (check-counter)))))

(define pname Name-name)

(set-pcontext!
  (lambda (context)
    (if (null? context)
        '()
        `(in ,(car context) ,@(pcontext (cdr context))))))

(set-pname*!
  (lambda (x)
    (if (null? (Name-context x))
        (Name-name x)
        (cons (Name-name x) (pcontext (Name-context x))))))

(define pname-rename
  (lambda (n)
    (let ([n (pname n)])
      (if (memq n primitives-to-rename)
          (symbol-append 'CF- n)
          n))))

(define pfn
  (lambda (e)
    (match e
      [(E: (Var x))
       (and (Name-primitive? x) (pname x))]
      [(E: (Lam: x _))
       (if (E-context e)
           (pname* (Define-name (E-context e)))
           `(lambda ,(map pname x) ...))]
      [(E: (Vlam: x rest _))
       (if (E-context e)
           (pname* (Define-name (E-context e)))
           `(lambda ,(append (map pname x) (pname rest)) ...))]
      [(E: (Letcc x _))
       `(letcc ,(pname x) ...)]
      [_ #f])))
