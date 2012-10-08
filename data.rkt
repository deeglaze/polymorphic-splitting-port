#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract Syntax definitions.

(require "library.rkt")
(provide (struct-out Define) make-Define
         (struct-out Defstruct)
         (struct-out Defmacro)
         (struct-out E) make-E like-E E:

         (struct-out And)
         (struct-out App)
         (struct-out Begin)
         (struct-out Const)
         (struct-out If)
         (struct-out Lam) Lam:
         (struct-out Let)
         (struct-out Clet)
         (struct-out Letr)
         (struct-out Or)
         (struct-out Set!)
         (struct-out Var)
         (struct-out Vlam) Vlam:
         (struct-out Letcc)

         (struct-out Name) make-Name

         (struct-out Primitive)
         (struct-out Simple)
         (struct-out Constructor)
         (struct-out Predicate)
         (struct-out Selector)
         (struct-out Mutator)

         empty-context empty-context? extend-context
         labeled? labelof extra-labels reset-labels!
         let-binder syntactic-letrec-group
         recursive-var? Name-unbound? Name-primitive? Name-let-bound? Name-rec-bound?
         Name-primop Name-binding definition-names)

;; bindings are defines, defstructs, defmacros, or expressions:

(struct Define (name exp) #:constructor-name construct-Define #:prefab)
(define make-Define
  (lambda (name exp)
    (let ([d (construct-Define name exp)])
      (unless (Name-binder name) (set-Name-binder! name d))
      (set-E-context! exp d)
      d)))
(struct Defstruct (tag con pred sels muts) #:prefab)
(struct Defmacro (def) #:prefab)
(struct E (exp context labels cont?) #:mutable #:prefab
        #:constructor-name construct-E)
(define-match-expander E: (syntax-rules () [(_ exp) (E exp _ _ _)]))
(define (make-E exp) (construct-E exp #f '() #f))
(define (like-E exp old-E)
  (construct-E exp #f (E-labels old-E) (E-cont? old-E)))


;; All expressions are wrapped in an E:

(struct And (exps) #:prefab)
(struct App (fun args) #:prefab)
(struct Begin (exps) #:prefab)
(struct Const (val) #:prefab)
(struct If (test then else) #:prefab)
(struct Lam (names exp [free #:auto #:mutable]) #:prefab #:auto-value #f)
(struct Let (bindings exp) #:prefab)
(struct Clet (names bindings exp) #:prefab)

(struct Letr (bindings exp) #:prefab)
(struct Or (exps) #:prefab)
(struct Set! (name exp) #:prefab)
(struct Var (name) #:prefab)
(struct Vlam (names rest exp [free #:auto #:mutable]) #:prefab #:auto-value #f)
(struct Letcc (name exp) #:prefab)

(define-match-expander Lam:
  (syntax-rules () [(_ names exp) (Lam names exp _)]))
(define-match-expander Vlam:
  (syntax-rules () [(_ names rest exp) (Vlam names rest exp _)]))


; Names in binding forms are:

(define name-counter (generate-counter 0))
(struct Name
  ([name #:mutable]                 ; symbol
   context                          ; list of symbols
   id                               ; unique identifier
   [binder #:mutable]               ; (E Lam), (E Vlam), (E Letcc), Define, Primitive or #f
   [component #:mutable]            ; list of Names in recursive binding component
   [mutated? #:mutable]             ; #t or #f
   [used-before-defined? #:mutable] ; #t or #f
   [cont? #:mutable]                ; #t if continuation variable
   [map #:mutable]) #:prefab)       ; the abstract variable map
(define (make-Name name context)
  (Name name context (name-counter) #f #f #f #f #f #f))

(define empty-context '())
(define empty-context? null?)
(define extend-context cons)

(struct Primitive (kind arity arg-types result-type can-be-simplified? purity)
        #:prefab)

; kind in Primitive =
(struct Simple () #:prefab)
(struct Constructor (tag) #:prefab)
(struct Predicate (tag) #:prefab)
(struct Selector (tag index) #:prefab)
(struct Mutator (tag index value-index) #:prefab)

;; Abstract operations on data structures

;; on Expressions

(define labeled? (lambda (e) (not (null? (E-labels e)))))

(define labelof (lambda (e) (car (E-labels e))))

(define extra-labels (lambda (e) (cdr (E-labels e))))

(define reset-labels! (lambda (e) (set-E-labels! e '())))

(define let-binder
  (lambda (e)
    (and (E-context e) (Define-name (E-context e)))))

;; Return #f or a list of Defines whose right hand sides are
;; syntactic lambdas such that this expression is one of them.
(define syntactic-letrec-group
  (lambda (e)
    (let ([x (let-binder e)])
      (and x
           (Name-rec-bound? x)
           (let ([defs (map Name-binder (Name-component x))])
             (and (andmap
                    (match-lambda
                      [(E (or (? Lam?) (? Vlam?)) _ _ _) #t]
                      [_ #f])
                    (map Define-exp defs))
                  defs))))))

;; on Vars

(define recursive-var?
  (lambda (e)
    (match e
      [(E (Var x) _ _ _)
       (and (not (Name-primitive? x)) (car (extra-labels e)))]
      [_ #f])))

;; on Names

(define Name-unbound?
  (lambda (n)
    (not (Name-binder n))))

(define Name-primitive?
  (lambda (n)
    (Primitive? (Name-binder n))))

(define Name-primop    ;; assumes Name-primitive? is true
  (lambda (n)
    (Primitive-kind (Name-binder n))))

(define Name-let-bound?
  (lambda (n)
    (Define? (Name-binder n))))

(define Name-binding   ;; assumes Name-let-bound? is true
  (lambda (n)
    (Define-exp (Name-binder n))))

(define Name-rec-bound? Name-component)

;; on definition lists

(define definition-names
  (lambda (defs)
    (for/fold ([names '()]) ([def (in-list defs)])
      (match def
        [(Define x _) (cons x names)]
        [(Defstruct _ con pred sels muts)
         `(,con ,pred ,@sels ,@(filter Name? muts) ,@names)]
        [_ names]))))
