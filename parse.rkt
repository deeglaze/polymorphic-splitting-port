#lang racket

(require "library.rkt"
         "data.rkt"
         "env.rkt"
         "r4rsprim.rkt"
         "components.rkt"
         "free.rkt"
         "check.rkt"
         "macros.rkt"
         "mutrec.rkt")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parsing and Binding References

(provide parse-def init-parse!)

;; This file exports:
;;  parse-def - for parsing a definition

;;  quote-env - an environment providing a binding for primitive quote
;;  basic-env - an environment providing bindings for basic forms

;;  special   - the #special symbol
;;  primitive - the #primitive symbol

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rest of parsing

(struct Keyword (def-fn exp-fn) #:prefab)
(struct Macro (fn) #:prefab)

;; Parsing definitions is hairy for two reasons.  First, defines are
;; recursive, so the environment for all defines must be built before
;; parsing their bodies.  Second, begin is heavily overloaded with
;; slightly different semantics in top-level, versus in a body,
;; versus in an expression.

(define r4rs-env empty-env)

;; Top level definition parser.  Allow arbitrary mixtures of definitions
;; and expressions, with begin just inlining the enclosed expressions
;; (begin does nothing at top-level but encapsulate a list of expressions
;; into a single syntactic entity).
;; Return a list of definitions, an environment, and list of unbound Names.
(define parse-def
  (lambda (x env primitive-env)
    (set! r4rs-env primitive-env)
    (let ([unbound '()])
      (set! note-unbound!
        (lambda (n) (set! unbound (cons n unbound))))
      (let loop ([xs '()]
                 [names '()]
                 [mkdef (lambda _ '())]
                 [unparsed (list x)])
        (cond
         [(null? unparsed)
          (define newenv (extend-env* env xs names))
          (define exps (mkdef newenv))
          (define defs (filter Define? exps))
          (ensure-no-repeats xs empty-context)
          (make-components! defs)
          (list exps newenv unbound)]
         [else
          (match-define (list xs2 names2 mkdef2 unparsed2)
                        (try-parse-def (car unparsed) env empty-context))
          (cond
           [(null? unparsed2)
            (loop (append xs xs2)
                  (append names names2)
                  (lambda (env)
                    (append (mkdef env) (mkdef2 env)))
                  (cdr unparsed))]
           [else
            (loop (append xs xs2)
                  (append names names2)
                  (lambda (env)
                    (append
                     (mkdef env)
                     (mkdef2 env)
                     (list (parse-exp (car unparsed2) env empty-context))))
                  (append (cdr unparsed2) (cdr unparsed)))])])))))

;; Definition parser for let and lambda bodies.  Any number of definitions may
;; be followed by one or more expressions, but no definitions can appear after
;; an expression.  Begin again just inlines.
(define parse-body
  (lambda (body env context)
    (match-let ([(list xs names mkdef unparsed)
                 (parse-begin `(begin ,@body) env context)])
      (when (null? unparsed)
        (syntax-err context #f "no expressions in body"))
      (ensure-no-repeats xs context)
      (let* ([newenv (extend-env* env xs names)]
             [defs (mkdef newenv)]
             [exps (for/list ([x (in-list unparsed)])
                     (parse-exp x newenv context))]
             [defines-only (filter Define? defs)])
        (make-components! defines-only)
        (let ([body (cond [(null? (cdr exps)) (car exps)]
                          [else (make-E (Begin exps))])])
          (cond [(null? defs) body]
                [else (make-E (Letr defs body))]))))))



;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define try-parse-def
  (lambda (x env context)
    (match x
      [(cons (? symbol? fun) args)
       (match (lookup? env fun)
         [(Keyword #f _) (list '() '() (lambda _ '()) (list x))]
         [(Keyword f _) (f x env context)]
         [(Macro f) (try-parse-def (f x env context) env context)]
         [_ (cond [(lookup? basic-env fun)
                   (error 'try-parse-def "(rebound?) Unsupported form: ~a" x)]
                  [else (list '() '() (lambda _ '()) (list x))])])]
      [_ (list '() '() (lambda _ '()) (list x))])))

;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define parse-define
  (lambda (x env0 context)
    (match x
      [(list _ (? symbol? s) e)
       (let ([n (make-Name s context)])
         (list (list s)
               (list n)
               (lambda (env)
                 (list (make-Define
                         n
                         (parse-exp e (if (eq? e s) env0 env) (extend-context s context)))))
               '()))]
      [(list-rest _ (cons (? symbol? s) args) body)
       (let ([n (make-Name s context)])
         (list (list s)
               (list n)
               (lambda (env)
                 (list (make-Define
                         n
                         (parse-lambda `(lambda ,args ,@body) env (extend-context s context)))))
               '()))]
      [_ (syntax-err context x "")])))

;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define parse-defstruct
  (lambda (x env context)
    (match x
      [(list _ (? symbol? tag) (? symbol? con) (? symbol? pred) fields ...)
       (let* ([sels (map (match-lambda
                           [(? symbol? x) x]
                           [(list (? symbol? x) (? symbol?)) x]
                           [_ (syntax-err context x "")])
                         fields)]
              [muts (map (match-lambda
                           [(? symbol? x) #f]
                           [(list (? symbol?) (? symbol? x)) x]
                           [_ (syntax-err context x "")])
                         fields)]
              [ncon (let ([n (make-Name con empty-context)]
                          [len (length sels)])
                      (set-Name-binder! n
                        (Primitive
                          (Constructor tag)
                          `(,len)
                          (make-list len '_)
                          (list tag)
                          #f
                          #f))
                      n)]
              [npred (let ([n (make-Name pred empty-context)])
                       (set-Name-binder! n
                         (Primitive
                           (Predicate (list tag))
                           '(1)
                           '(_)
                           '(true false)
                           #f
                           #f))
                       n)]
              [nsels (map-with-n
                       (lambda (x i)
                         (let ([n (make-Name x empty-context)])
                           (set-Name-binder! n
                             (Primitive
                               (Selector tag i)
                               '(1)
                               `((,tag))
                               '()
                               #f
                               'R))
                           n))
                       sels)]
              [nmuts (map-with-n
                       (lambda (x i)
                         (and x (let ([n (make-Name x empty-context)])
                                  (set-Name-binder! n
                                    (Primitive
                                      (Mutator tag i 1)
                                      '(2)
                                      `((,tag) _)
                                      '()
                                      #f
                                      'W))
                                  n)))
                       muts)]
              [xs `(,con ,pred ,@sels ,@(filter (lambda (x) x) muts))]
              [names `(,ncon ,npred ,@nsels ,@(filter (lambda (x) x) nmuts))])
         (list xs
               names
               (lambda (env)
                 (list (Defstruct tag ncon npred nsels nmuts)))
               '()))]
      [_ (syntax-err context x "")])))

;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define parse-defmacro
  (lambda (x env context)
    (match x
      [(list-rest _ (? symbol? name) _)
       (printf "Note: installing but _not_ checking (defmacro ~a ...)~%" name)
       (eval x)
       (list '() '() (lambda (env) (list (Defmacro x)) '()) '())]
      [_ (syntax-err context x "")])))

;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define parse-begin
  (lambda (x env context)
    (match x
      [(cons _ exps)
       (let loop ([exps exps]
                  [xs '()]
                  [names '()]
                  [mkdef (lambda _ '())]
                  [unparsed '()])
         (if (or (null? exps) (not (null? unparsed)))
             (list xs names mkdef (append unparsed exps))
             (match-let ([(list xs2 names2 mkdef2 unparsed2)
                          (try-parse-def (car exps) env context)])
               (loop (cdr exps)
                     (append xs xs2)
                     (append names names2)
                     (lambda (env) (append (mkdef env) (mkdef2 env)))
                     unparsed2))))]
      [_ (syntax-err context x "")])))

;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define parse-n-primitive-as-def
  (lambda (x env context)
    (match x
      [(list-rest _ (? symbol? s) args)
       (match (lookup? r4rs-env s)
         [(Keyword #f _) (list '() '() (lambda _ '()) (list x))]
         [(Keyword f _) (f (cdr x) env context)]
         [(Macro f) (try-parse-def (f x env context) env context)]
         [_ (list '() '() (lambda _ '()) (list x))])]
      [_ (syntax-err context x "")])))

;; returns list of x's, list of names, env -> list of Defines, list of unparsed exps
(define parse-n-special-as-def
  (lambda (x env context)
    (match x
      [(list-rest _ (? symbol? s) args)
       (match (lookup? special-env s)
         [(Keyword #f _) (list '() '() (lambda _ '()) (list x))]
         [(Keyword f _) (f (cdr x) env context)]
         [(Macro f) (try-parse-def (f x env context) env context)]
         [_ (list '() '() (lambda _ '()) (list x))])]
      [_ (syntax-err context x "")])))

(define parse-exp
  (lambda (x env context)
    (match x
      [(? box?)                (parse-exp (quote-tf x env context) env context)]
      [(? vector?)             (parse-exp (quote-tf x env context) env context)]
      [(? boolean?)            (make-E (Const x))]
      [(? null?)               (make-E (Const x))]
      [(? number?)             (make-E (Const x))]
      [(? char?)               (make-E (Const x))]
      [(? string?)             (make-E (Const x))]
      [(? symbol?)             (make-E (Var (parse-name x env context)))]
      [(cons fun args)
       (if (symbol? fun) ;; user-bound function call, macro or primitive call
           (match (lookup? env fun)
             [(Keyword _ #f) (syntax-err context #f "invalid context for ~a" x)]
             [(Keyword _ f) (f x env context)]
             [(Macro f) (parse-exp (f x env context) env context)]
             [(? Name? n) (parse-app x env context)]
             [else (cond [(lookup? basic-env fun)
                          (parse-app x env context)]
                         [else (error 'parse-exp "Unsupported form: ~a (~a)" x else)])])
           (parse-app x env context))]
      [_ (syntax-err context x "parse-exp")])))

(define parse-app
  (lambda (x env context)
    (match x
      [(cons fun args)
       (make-E (App
         (parse-exp fun env context)
         (map (lambda (x) (parse-exp x env context)) args)))]
      [_ (syntax-err context x "parse-app")])))

(define parse-lambda
  (lambda (x env context)
    (match x
      [(list-rest _ bindings body)
       (let loop ([b bindings] [vars '()])
         (match b
           [(? symbol? rest)
            (let* ([all (cons rest vars)]
                   [names (map (lambda (n) (make-Name n context)) all)]
                   [new-env (extend-env* env all names)]
                   [body (parse-body body new-env context)]
                   [e (make-E (Vlam (reverse (cdr names)) (car names) body))])
              (ensure-no-repeats all context)
              (for-each
                (lambda (n) (set-Name-binder! n e))
                names)
              e)]
           ['()
            (let* ([names (map (lambda (n) (make-Name n context)) vars)]
                   [new-env (extend-env* env vars names)]
                   [body (parse-body body new-env context)]
                   [e (make-E (Lam (reverse names) body))])
              (ensure-no-repeats vars context)
              (for ([n (in-list names)])
                ;; Each variable points to which binding form binds it
                (set-Name-binder! n e))
              e)]
           [(cons (? symbol? n) x)
            (loop x (cons n vars))]
           [_ (syntax-err context x "in lambda expression")]))]
      [_ (syntax-err context x "parse-lambda")])))

(define parse-if
  (lambda (x env context)
    (match x
      [(list _ test then els)
       (let* ([test (parse-exp test env context)]
              [then (parse-exp then env context)]
              [els (parse-exp els env context)]
              [%not? (lambda (x) (eq? x %not))])
         (let loop ([test test] [then then] [els els])
           (match test
             [(E: (App (E: (Var (? %not?))) (list not-test)))
              (loop not-test els then)]
             [_ (make-E (If test then els))])))]
      [(list _ test then)
       (when if-warning
         (printf "Note: one-armed if: ")
         (pretty-print x))
       (make-E (If
                 (parse-exp test env context)
                 (parse-exp then env context)
                 (parse-exp '(void) env context)))]
      [_ (syntax-err context x "parse-if")])))

(define parse-set!
  (lambda (x env context)
    (match x
      [(list _ (? symbol? s) exp)
       (let ([n (parse-name s env context)])
         (when (Name-primitive? n)
           (syntax-err context x "cannot set! primitive"))
         (make-E (Set! n (parse-exp exp env context))))]
      [_ (syntax-err context x "parse-set!")])))

(define parse-and
  (lambda (x env context)
    (match x
      [(cons _ exps)
       (make-E (And (map (lambda (x) (parse-exp x env context)) exps)))]
      [_ (syntax-err context x "parse-and")])))

(define parse-or
  (lambda (x env context)
    (match x
      [(cons _ exps)
       (make-E (Or (map (lambda (x) (parse-exp x env context)) exps)))]
      [_ (syntax-err context x "parse-or")])))

(define parse-let
  (lambda (x env context)
    (match x
      [(list-rest _ (? symbol? n) (list (list (? symbol? vars) exps) ...) body)
       ;; following is the right translation but it is compiled poorly
       '(parse-exp `((letrec ([,n (lambda ,vars ,@body)]) ,n) ,@exps) env context)
       (parse-exp `(letrec ([,n (lambda ,vars ,@body)]) (,n ,@exps)) env context)]
      [(list-rest _ (list (list (? symbol? vars) exps) ...) body)
       (ensure-no-repeats vars context)
       (let* ([names (map (lambda (s) (make-Name s context)) vars)]
              [new-env (extend-env* env vars names)]
              [bindings (map (lambda (name e)
                               (make-Define
                                 name
                                 (parse-exp e env
                                            (extend-context (Name-name name) context))))
                             names
                             exps)]
              [e (make-E (Let bindings (parse-body body new-env context)))])
         e)]
      [_ (syntax-err context x "parse-let")])))

(define parse-letrec
  (lambda (x env context)
    (match x
      [(list-rest _ (list (list (? symbol? vars) exps) ...) body)
       (ensure-no-repeats vars context)
       (let* ([names (for/list ([s (in-list vars)]) (make-Name s context))]
              [new-env (extend-env* env vars names)]
              [bindings (for/list ([name (in-list names)]
                                   [e (in-list exps)])
                          (make-Define
                           name
                           (parse-exp e new-env (extend-context (Name-name name) context))))]
              [e (make-E (Letr bindings (parse-body body new-env context)))])
         (make-components! bindings)
         e)]
      [_ (syntax-err context x "parse-letrec")])))

(define parse-letcc
  (lambda (x env context)
    (match x
      [`(,_ ,(? symbol? s) ,exps __1)
       (let* ([name (make-Name s context)]
              [new-env (extend-env env s name)]
              [e (make-E (Letcc
                           name
                           (make-E (Begin
                                     (map (lambda (x) (parse-exp x new-env context)) exps)))))])
         (set-Name-binder! name e)
         e)]
      [_ (syntax-err context x "parse-letcc")])))

(define parse-begin-exp
  (lambda (x env context)
    (match x
      [(list _ exp)
       (parse-exp exp env context)]
      [(list _ exps __1)
       (make-E (Begin (map (lambda (x) (parse-exp x env context)) exps)))]
      [_ (syntax-err context x "parse-begin-exp")])))

(define parse-quote-symbol
  (lambda (x env context)
    (match x
      [(list _ (? symbol? s)) (make-E (Const s))]
      [_ (syntax-err context x "parse-quote-symbol")])))

(define parse-n-primitive
  (lambda (x env context)
    (match x
      [(list-rest _ (? symbol? s) args)
       (match (lookup? r4rs-env s)
         [(Keyword _ #f) (syntax-err context #f "invalid context for ~a" x)]
         [(Keyword _ f) (f (cdr x) env context)]
         [(Macro f) (parse-exp (f (cdr x) env context) env context)]
         [(? Name?) (if (null? args)
                        (parse-exp s r4rs-env context)
                        (syntax-err context x "n-primitive args"))]
         [_ (syntax-err context #f "~a is not a primitive" s)])]
      [_ (syntax-err context x "parse-n-primitive")])))

(define parse-n-special
  (lambda (x env context)
    (match x
      [(list-rest _ (? symbol? s) args)
       (match (lookup? special-env s)
         [(Keyword _ #f) (syntax-err context #f "invalid context for ~a" x)]
         [(Keyword _ f) (f (cdr x) env context)]
         [(Macro f) (parse-exp (f (cdr x) env context) env context)]
         [(? Name?) (if (null? args)
                        (parse-exp s special-env context)
                        (syntax-err context x "parse-n-special args"))]
         [_ (syntax-err context #f "~a is not a special" s)])]
      [_ (syntax-err context x "parse-n-special")])))

(define parse-name
  (lambda (x env context)
    (match (lookup? env x)
      [(? Keyword?) (syntax-err context #f "invalid use of keyword ~a" x)]
      [(? Macro?) (syntax-err context #f "invalid use of macro ~a" x)]
      [#f (define n (make-Name x context))
          (printf "Warning: ~a (~a) is unbound~%" (pname* n) x)
          (note-unbound! n)
          n]
      [n n])))

(define note-unbound!
  (lambda (n) (error 'parse "UNBOUND")))

(define ensure-no-repeats
  (lambda (l context)
    (match (repeated l)
      [#f #f]
      [name (syntax-err context #f "~a is bound more than once" name)])))

(define (alist->env alst [base empty-env])
  (for/fold ([env base]) ([(key val) (in-dict alst)])
     (extend-env env key val)))

(define (init-parse!)
  (set-quote-env!
   (alist->env `((quote . ,(Keyword #f parse-quote-symbol)))))

  (set-basic-env!
   (alist->env
    (let ([qq 'quasiquote])
      `((quote . ,(Macro quote-tf))
        (,qq . ,(Macro quasiquote-tf))
        (box . ,(Macro quote-tf))
        (vector . ,(Macro quote-tf))
        (let* . ,(Macro let*-tf))
        (cond . ,(Macro cond-tf))
        (case . ,(Macro case-tf))
        (do . ,(Macro do-tf))
        (delay . ,(Macro delay-tf))
        (recur . ,(Macro recur-tf))
        ;; Keywords
        (lambda . ,(Keyword #f parse-lambda))
        (if . ,(Keyword #f parse-if))
        (set! . ,(Keyword #f parse-set!))
        (and . ,(Keyword #f parse-and))
        (or . ,(Keyword #f parse-or))
        (let . ,(Keyword #f parse-let))
        (letrec . ,(Keyword #f parse-letrec))
        (letcc . ,(Keyword #f parse-letcc))
        (begin . ,(Keyword parse-begin parse-begin-exp))
        (define . ,(Keyword parse-define #f))
        (defstruct . ,(Keyword parse-defstruct #f))
        (defmacro . ,(Keyword parse-defmacro #f))
        (,primitive . ,(Keyword parse-n-primitive-as-def parse-n-primitive))
        (,special . ,(Keyword parse-n-special-as-def parse-n-special))))
    quote-env)))
