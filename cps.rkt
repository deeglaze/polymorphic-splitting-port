#lang racket

(require "library.rkt"
         "components.rkt"
         "mutrec.rkt"
         "data.rkt")
(provide cps-tree cps? set-cps?! init-cps!)

(define init-cont-name #f)
(define init-cont-def #f)
(define init-cont #f)

(define cps? #f)
(define (set-cps?! v) (set! cps? v))

(define (init-cps!)
  (define init-kvar (make-new-cont-arg))
  (set-cps?! #t)
  (set! init-cont (make-E (Lam (list init-kvar)
                                      (make-E (Var init-kvar)))))
  (set-E-cont?! init-cont #t)
  (set-Name-binder! init-kvar init-cont)
  (set! init-cont-name (make-new-cont-var))
  (set! init-cont-def (make-Define init-cont-name init-cont)))

(define (trivial? exp)
  (let ([triv-folder (lambda (args)
                       (for/and ([arg (in-list args)]) (trivial? arg)))])
    (match exp
	   [(Define x e) (trivial? e)]
	   [(E: (or (? Const?) (? Var?))) #t]
	   [(E: (Letr bindings body))
	    (and (triv-folder bindings) (trivial? body))]
	   [(E: (Let bindings body))
	    (and (triv-folder bindings) (trivial? body))]
	   [(E: (App e0 args))
	    (match e0
		   [(E: (Var x))
		    (and (Name-primitive? x) (triv-folder args))]
		   [_ #f])]
	   [else #f])))

(define (gen-cont)
  (gensym "K"))

(define (gen-cont-arg)
  (gensym "V"))

(define (make-new-cont-var)
  (let [(name (make-Name (gen-cont) '(cont)))]
    (set-Name-cont?! name #t)
    name))

(define (make-new-cont-arg)
  (make-Name (gen-cont-arg) '(cont)))

(define (cont-var? name)
  (and (Name? name) (memq 'cont (Name-context name))))

(define (make-cont-args n)
  (let loop ((i 0)
	     (vars '()))
    (cond ((= i n) vars)
	  (else (loop (+ i 1) (cons (make-new-cont-arg) vars))))))

(define (cont-folder f i j k)
  (cond [(or (null? k) (null? j)) i]
	[else (cont-folder f (f i (car j) (car k)) (cdr j) (cdr k))]))


(define (apply-cont k . e)
  (cond [(eq? k init-cont) (car e)]
	[else (let* ([new (make-new-cont-var)]
		     [var-new (make-E (Var new))]
		     [newk (cond [(Name? k)
				  (make-E (Var k))]
				 [else k])])
		(match newk
		       [(E: (? Lam?))
			(let ([d (make-Define new newk)])
			  (set-Name-binder! new d)
			  (make-E (Let
				   (list d)
				   (make-E (App var-new e)))))]
		       [else (make-E (App newk e))]))]))

(define (add-cont k args)
  (cond [(eq? k init-cont) (cons (make-E (Var init-cont-name)) args)]
	[else (cons (if (Name? k) (make-E (Var k)) k) args)]))

(define (filter-false l)
  (filter (lambda (x) (not (eq? x #f))) l))

(define (restrict proc l)
  (filter (lambda (l) (not (proc l))) l))

(define (make-continuation var body)
  (let ([cont (make-E (Lam (list var) body))])
    (set-Name-binder! var cont)
    (set-E-cont?! cont #t)
    cont))

(define (cps exp k)
  (match exp
	 [(Define x e)
	  (set-Name-binder! x #f)
	  (make-Define x (cps e k))]
	 [(or (E: (? Const?)) (E: (? Var?)))
	  (apply-cont k exp)]
	 [(E: (Lam: args body))
	  (let* ([new-k (make-new-cont-var)]
		 [args (cons new-k args)]
		 [newBody (cps body new-k)]
		 [newLam (make-E (Lam args newBody))])
	    (for-each (lambda (n) (set-Name-binder! n newLam)) args)
	    (apply-cont k newLam))]
	 [(E: (Vlam: args rest body))
	  (let* ([new-k (make-new-cont-var)]
		 [args (cons new-k args)]
		 [newLam (make-E (Vlam args
					    rest
					    (cps body new-k)))])
	    (for-each (lambda (n) (set-Name-binder! n newLam)) args)
	    (set-Name-binder! rest newLam)
	    (apply-cont k newLam))]
	 [(E: (App e0 args))
	  (let ([folder (lambda (init args cont-vars)
			  (cont-folder
			   (lambda (exp j v)
			     (cps j (make-continuation v exp)))
			   init
			   args
			   cont-vars))]
		[simple-cps (lambda (args)
			      (mapLR (match-lambda
				      [(and lam (E: (Lam: names body)))
				       (let ([new-k (make-new-cont-arg)])
					 (set-Name-binder! new-k lam)
					 (cps lam new-k))]
				      [e e])
				     args))]
		[contName->var (lambda (k)
				 (if (Name? k)
				     (make-E (Var k))
				     k))])
	    (cond [(trivial? exp) (apply-cont k exp)]
		  [else
		   (match e0
			  [(E: (Var x))
			   (=> cont)
			   (if (Name-primitive? x)
			       (let ([cont-vars (make-cont-args (length args))])
				 (folder
				  (apply-cont k (make-E
						 (App
						  e0
						  (map (lambda (n)
							 (make-E (Var n)))
						       cont-vars))))
				  args
				  cont-vars))
			       (cont))]
			  [_ (let* ([terms (cons e0 args)]
				    [argList
				     (mapLR (lambda (arg)
					      (if (trivial? arg)
						  arg
						  (make-new-cont-arg)))
					    terms)]
				    [cont-vars
                                     (for/fold ([acc '()]) ([arg (in-list argList)]
                                                            #:when (cont-var? arg))
                                       (cons arg acc))])
			       (cond [(null? cont-vars)
				      (match e0
					     [(E: (Lam: formals body))
					      (make-E (App
						       (make-E (Lam
								formals
								(cps body k))))
						       (simple-cps args))]
					     [(E: (Vlam: formals rest body))
					      (make-E (App (make-E (Vlam
									 formals
									 rest
									 (cps body k)))
								(simple-cps args)))]
					     [else
					      (make-E (App
						       e0
						       (cons (contName->var k)
							     (simple-cps args))))])]
				     [else (let ([argList (mapLR contName->var argList)])
					     (cont-folder
					      (lambda (e j v)
						(cps j (make-continuation v e)))
					      (make-E (App
						       (car argList)
						       (cons (contName->var k)
							     (cdr argList))))
					      (restrict trivial? (cons e0 args))
					      (reverse cont-vars)))]))])]))]
	 [(E: (If pred then els))
	  (let* ([v (make-new-cont-arg)]
		 [newk (make-new-cont-arg)]
		 [var (lambda () (make-E (Var newk)))]
		 [b (make-Define newk (if (Name? k) (make-E (Var k)) k))])
	    (set-Name-binder! newk b)
	    (make-E (Let
		     (list b)
		     (if (trivial? pred)
			 (make-E (If pred
					  (cps then (var))
					  (cps els (var))))
			 (cps pred (make-continuation
				    v
				    (make-E (If (make-E (Var v))
						     (cps then (var))
						     (cps els (var))))))))))]
	 [(E: (Let bindings body))
	  (let* ([names (mapLR (match-lambda
				[(Define name e) name])
			       bindings)]
		 [args (mapLR (match-lambda
			       [(Define name e) e])
			      bindings)]
		 [lam (make-E (Lam names body))])
	    (for-each (lambda (n) (set-Name-binder! n lam)) names)
	    (cps (make-E (App lam args)) k))]
	 [(E: (Letr bindings body))
	  (let* ([defs  (mapLR (lambda (b) (cps b init-cont))  bindings)])
	    (make-components! (filter Define? defs))
	    (make-E (Letr defs (cps body k))))]
	 [(E: (Set! x e))
	  (let ([v (make-new-cont-arg)])
	    (cps e (make-continuation
		    v
		    (apply-cont k (make-E (Set! x (make-E (Var v))))))))]
	 [(E: (Begin exps))
	  (let ([names (make-cont-args (length exps))]
		[defs (filter Define? exps)])
	    (cont-folder (lambda (e j v)
			   (cps j (make-continuation v e)))
			 (apply-cont k (make-E (Var (car names))))
			 (reverse exps)
			 names))]
	 [(E: (And exps))
	  (let* ([rexps (reverse exps)]
		 [new
                  (for/fold ([acc (car rexps)])
                      ([e (in-list (cdr rexps))])
                    (make-E (If e acc (make-E (Const #f)))))])
	    (cps new k))]
	 [(E: (Or exps))
	  (let* ([rexps (reverse exps)]
		 [new
                  (for/fold ([acc (car rexps)])
                      ([e (in-list (cdr rexps))])
                    (define new (make-new-cont-var))
                    (make-E (Let (list (make-Define new e))
                                 (make-E (If (make-E (Var new))
                                             (make-E (Var new))
                                             acc)))))])
	    (cps new k))]
	 [else exp]))

(define (cps-tree)
  (match tree
	 [(E: (Letr bindings body))
	  (let* ([new-exps (mapLR (lambda (b) (cps b init-cont)) bindings)]
		 [real-defs (cons init-cont-def (filter Define? new-exps))]
		 [new-tree (make-E (Letr (cons init-cont-def new-exps) body))])
	    (make-components! real-defs)
	    (set-tree! new-tree))]))


