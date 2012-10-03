#lang racket

(require "library.rkt"
         "env.rkt"
         "mutrec.rkt"
         "data.rkt")
(provide install-contour! print-contour make-initial-contour
         let-binding-contour context->contour var-split
         make-closure-contour aval-type
         make-type-based-contours
         call-site-contour if-contour rec-contour
         Type contour-length
         make-context)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Contours
;;
;; Several separate contour abstractions are contained in this file.
;; One for polymorphic splitting, one for old polymorphic splitting,
;; one for call strings, and one for typed splitting.

(define Call #f)
(define Type #f)
(define Cont #f)

(define install-contour!
  (match-lambda
    ['full-poly (begin
                  (set! make-closure-contour poly-make-closure-contour)
                  (set! var-split poly-var-split)
                  (set! let-binding-contour no-let-binding-contour)
                  (set! call-site-contour poly-call-site-contour)
                  (set! make-context triv-make-context)
                  (set! context->contour triv-context->contour)
                  (set! Type #f)
		  (set! Cont #f)
                  (set! Call #f))]
    ['poly      (begin
                  (set! make-closure-contour poly-make-closure-contour)
                  (set! var-split old-poly-var-split)
                  (set! let-binding-contour old-poly-let-binding-contour)
                  (set! call-site-contour poly-call-site-contour)
                  (set! make-context triv-make-context)
                  (set! context->contour triv-context->contour)
                  (set! Type #f)
		  (set! Cont #f)
                  (set! Call #f))]
    ['cf0       (begin
                  (set! make-closure-contour simple-make-closure-contour)
                  (set! var-split no-var-split)
                  (set! let-binding-contour no-let-binding-contour)
                  (set! call-site-contour simple-call-site-contour)
                  (set! make-context full-make-context)
                  (set! context->contour full-context->contour)
                  (set! Type #f)
		  (set! Cont #f)
                  (set! Call #f))]
    ['cf1       (begin
                  (set! make-closure-contour simple-make-closure-contour)
                  (set! var-split no-var-split)
                  (set! let-binding-contour no-let-binding-contour)
                  (set! call-site-contour call-call-site-contour)
                  (set! make-context full-make-context)
                  (set! context->contour full-context->contour)
                  (set! Type #f)
		  (set! Cont #f)
                  (set! Call 1))]
    [`(cf ,(? number? n))
                (begin
                  (set! make-closure-contour simple-make-closure-contour)
                  (set! var-split no-var-split)
                  (set! let-binding-contour no-let-binding-contour)
                  (set! call-site-contour call-call-site-contour)
                  (set! make-context full-make-context)
                  (set! context->contour full-context->contour)
                  (set! Type #f)
		  (set! Cont #f)
                  (set! Call n))]
    [`(type ,(? number? n))
                (begin
                  (set! make-closure-contour simple-make-closure-contour)
                  (set! var-split no-var-split)
                  (set! let-binding-contour no-let-binding-contour)
                  (set! call-site-contour simple-call-site-contour)
                  (set! make-context full-make-context)
                  (set! context->contour full-context->contour)
                  (set! Type n)
                  (set! Call #f))]
    ['cont     (begin
                  (set! make-closure-contour simple-make-closure-contour)
                  (set! var-split no-var-split)
                  (set! let-binding-contour let-binding-contour)
                  (set! call-site-contour simple-call-site-contour)
                  (set! make-context triv-make-context)
                  (set! context->contour triv-context->contour)
                  (set! Type #f)
		  (set! Cont #t)
                  (set! Call #f))]
    [`(random ,(? number? n))
                (begin
                  (set! make-closure-contour simple-make-closure-contour)
                  (set! var-split no-var-split)
                  (set! let-binding-contour no-let-binding-contour)
                  (set! call-site-contour (make-random-call-site-contour n))
                  (set! make-context full-make-context)
                  (set! context->contour full-context->contour)
                  (set! Type #f)
		  (set! Cont #f)
                  (set! Call #f))]
    [x (error 'install-contour "unknown control ~a" x)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Actions for variable reference, let binding, and application

(define make-initial-contour
  (lambda () (vector)))

(define simple-make-closure-contour
  (lambda (k) (vector)))

(define simple-call-site-contour
  (lambda (l k vk)
    (context->contour k)))

(define triv-make-context
  (lambda (contour aenv) contour))

(define triv-context->contour
  (lambda (x) x))

(define full-make-context
  (lambda (contour aenv)
    (cons contour (env-range aenv))))

(define full-context->contour car)

;;;;;;;;;;;;;;;;
;; No splitting at all (0CFA)

(define no-var-split
  (lambda (x aenv l k let-label recursive? component)
    (let ([p (index-var-map x (lookup aenv x))])
      (result-map= l k p)
      p)))

(define no-let-binding-contour
  (lambda (k l)
    k))

;;;;;;;;;;;;;;;;
;; Call strings

(define call-call-site-contour
  (lambda (l k vk)
    (call-contour (context->contour k) l)))

;;;;;;;;;;;;;;;;
;; SAS style splitting

(define poly-make-closure-contour
  (lambda (x) (context->contour x)))

(define old-poly-var-split
  (lambda (x aenv l k let-label recursive? component)
    (let ([p (index-result-map l k)]
          [make-contour (if recursive?
                            (let ([c (context->contour k)])
                              (lambda (vk) (old-rec-contour vk let-label c)))
                            (lambda (vk) (old-var-contour vk let-label l)))])
      (p-> (index-var-map x (lookup aenv x))
           (lambda (new) (p+avals p (split new make-contour))))
      p)))

(define old-poly-let-binding-contour
  (lambda (k l)
    (let ((n (vector-length k)))
      (vector-tabulate
        (+ 1 n)
        (lambda (i)
          (if (< i n)
              (vector-ref k i)
              l))))))

(define poly-call-site-contour
  (lambda (l k vk)
    vk))

;;;;;;;;;;;;;;;;
;; Type based splitting

(define contour-length vector-length)

(define make-type-based-contours
  (lambda (types current-contour)
    (define permute
      (lambda (l)
        (cond [(null? l) '()]
              [(null? (cdr l)) (map list (car l))]
              [(null? (car l)) '()]
              [else (let ([rest (permute (cdr l))])
                      (foldr
                        (lambda (m a)
                          (append
                            (map (lambda (r) (cons m r)) rest)
                            a))
                        '()
                        (car l)))])))
    (define extend-contour
      (lambda (k type)
        (let ([n (vector-length k)])
          (vector-tabulate
            (+ 1 n)
            (lambda (i)
              (if (< i n)
                  (vector-ref k i)
                  type))))))
    (map
      (lambda (arg-type-list)
        (extend-contour current-contour arg-type-list))
      (permute types))))

(define (aval-type aval)
  (cond [(eq? (aval-kind aval) 'closure)
	 (aval-label aval)]
	[else (aval-kind aval)]))

;;;;;;;;;;;;;;;;
;; Full polymorphic splitting

(define poly-var-split
  (lambda (x aenv l k let-label recursive? component)
    (cond [(and (not recursive?)
                (andmap
                  (lambda (c)
                    (and (Name-let-bound? c)
                         (match (Name-binding c)
                           [(E: (or (? Lam?) (? Vlam?))) #t]
                           [_ #f])))
                  component))
           (let* ([old-k (lookup aenv x)]
                  [new-k (var-contour k l)]
                  [make-contour (lambda (vk) new-k)])
             (unless (equal? old-k new-k)
               (for-each
                 (lambda (y)
                   (let ([q (index-var-map y new-k)])
                     (p-> (index-var-map y old-k)
                          (lambda (new)
                            (p+avals q (split-env new component make-contour))))))
                 component))
             ;; take advantage of the fact that the component includes us
             (let ([p (index-var-map x new-k)])
               (result-map= l k p)))]
          [else
           (let ([p (index-var-map x (aenv-lookup aenv x))])
             (result-map= l k p))])))

;;;;;;;;;;;;;;;;
;; Random

(define make-random-call-site-contour
  (lambda (n)
    (lambda (l k vk)
      (random n))))

;;;;;;;;;;;;;;;;
;; Parameters

(define var-split no-var-split)
(define let-binding-contour no-let-binding-contour)
(define make-closure-contour simple-make-closure-contour)
(define call-site-contour simple-call-site-contour)
(define make-context full-make-context)
(define context->contour full-context->contour)

(install-contour! 'poly)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Contour construction

;; Build a new contour at a variable reference.
(define old-var-contour
  (lambda (k old-l new-l)
    (vector-tabulate
      (vector-length k)
      (lambda (i)
        (let ((l (vector-ref k i)))
          (if (= l old-l)
              new-l
              l))))))

;; Build a new contour at a recursive variable reference.
(define old-rec-contour
  (lambda (k old-l current-k)
    (vector-tabulate
      (vector-length k)
      (lambda (i)
        (let ((l (vector-ref k i)))
          (if (= l old-l)
              (vector-ref current-k i)
              l))))))

;; Build a new contour at a variable reference.
(define max-contour 4000)
(define var-contour
  (lambda (k l)
    (let ([n (vector-length k)])
      (vector-tabulate
        (min (+ 1 n) max-contour)
        (lambda (i)
          (if (zero? i)
              l
              (vector-ref k (- i 1))))))))

;; Build a new contour at a recursive variable reference.
(define rec-contour
  (lambda (k current-k)
    (vector-tabulate
      (+ 1 (vector-length k))
      (lambda (i)
        (vector-ref current-k i)))))

;; Build a new call contour.
(define call-contour
  (lambda (k l)
    (vector-tabulate
      (min Call (+ 1 (vector-length k)))
      (lambda (i)
        (if (zero? i)
            l
            (vector-ref k (- i 1)))))))

;; Build a new if contour.
(define if-contour
  (lambda (k l)
    (cons l k)))

;; Turn a contour into a printable representation
(define print-contour
  (lambda (k) k))

;; Build a new call contour (for CPS'ed programs)

;(define (false? e) (eq? e #f))
;(define (true? e) (cond ((list? e)
;			 (if (not (null? e))
;			     #t #f))
;			(else e)))
;
;(define call-cont-contour
;  (lambda (l k _)
;    (let ([get-cont-label
;	   (lambda (kont)
;	     (let* ([points (index-result-map (labelof kont) k)]
;		    [avals (point-elements points)])
;	       (aval-label (car avals))))]
;	  [build-contour
;	   (lambda (kont)
;	     (let* ([l     (labelof kont)]
;		    [p     (index-result-map l k)]
;		    [avals (point-elements p)]
;		    [v (if (true? avals) (car avals) #f)])
;	       (cond [v (let* ([env (aval-env v)])
;			  (list->vector
;			   (cons l
;				 (filter-false
;				  (mapLR (match-lambda
;					  [(name . contour)
;					   (cond [(Name-cont? name)
;						  (let* ([p (index-var-map name contour)]
;							 [avals (point-elements p)])
;						    (if avals
;							(aval-label (car avals))
;							#f))]
;						 [else #f])])
;					 (env->list env))))))]
;		     [else k])))])
;      (match (label->node l)
;	     [($ E ($ App fun args))
;	      (let ([kont (if (true? args) (car args) #f)])
;		(match kont
;		       [($ E (? Lam?))
;			(if (true? (E-cont? kont))
;			    (build-contour kont)
;			    k)]
;		       [($ E ($ Var x))
;			(let* ([label (get-cont-label kont)]
;			       [kont (label->node label)])
;			  (if (and (E? kont) (true? (E-cont? kont)))
;			      (build-contour kont)
;			      k))]
;		       [else k]))]))))
;


(define (false? e) (eq? e #f))
(define (true? e) (cond ((list? e)
			 (if (not (null? e))
			     #t #f))
			(else e)))

(define (make-cont-based-contour v)
  (let* ([env (aval-env v)]
	 [l (aval-label v)]
	 [fv
          (for/fold ([acc (list l)])
              ([nc (in-list env)])
            (match nc
              [(cons name contour)
               (let* ([p (index-var-map name contour)]
                      [v (point-elements p)]
                      [kenv (list->set
                             (filter values
                                     (mapLR (lambda (av)
                                              (let ([l (aval-label av)])
                                                (and (E? (label->node l))
                                                     (E-cont? (label->node l))
                                                     l)))
                                            v)))])
                 (if (true? kenv) (list->set (append acc kenv)) acc))]))])
    (apply vector fv)))


