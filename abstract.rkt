#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operations implementing abstract values, environments, etc.

(require "library.rkt"
         "env.rkt"
         "callmap.rkt"
         "contour.rkt"
         "histo.rkt"
         "flags.rkt"
         "intset.rkt"
         "data.rkt"
         "queue.rkt"
         "mutrec.rkt")

(provide init-abstract!
         aval-contour aval-env aval-fields aval-is-simple?
         aenv-empty aenv-extend aenv-extend* aenv-restrict
         p+aval aval
         p->p p->1
         in-avals? except-avals except-in-avals? list->avals
         values-at-var values-at-label
         contours-at-var
         filter-avals
         propagate-across-edges!
         init-abstract-statistics!
         print-point)

;; Initialization operations

(define init-abstract!
  (lambda ()
    (init-aval!)
    (init-result-map!)
    (init-var-map!)
    (init-work-q!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The label result map, Label x Contour -> Point.
;; Implemented as a vector indexed by label of association lists.

(define result-map (vector '()))

(define init-result-map!
  (lambda ()
    (set! result-map (make-vector n-labels '()))))

(set-index-result-map!
  (lambda (l k)
    (let* ([q (vector-ref result-map l)]
           [r (assoc k q)])
      (if r
          (cdr r)
          (let ((v (make-empty-point l k)))
            (vector-set! result-map l (cons (cons k v) q))
            v)))))

;; Try to set the point for <l,k> to p.  We may not be able
;; to do this if the point for <l,k> has already been demanded.
(set-result-map=!
  (lambda (l k p)
    (let* ([q (vector-ref result-map l)]
           [r (assoc k q)])
      (if r
          (p->p p (cdr r))
          (begin (vector-set! result-map l (cons (cons k p) q))
		 p)))))

(set-contours-at-label!
  (lambda (l)
    (map car (vector-ref result-map l))))

(define points-at-label
  (lambda (l)
    (map cdr (vector-ref result-map l))))

(define values-at-label
  (lambda (l)
    (for/fold ([is (intset-make-empty)]) ([p (in-list (points-at-label l))])
      (intset-union is (point-elements p)))))

(define reached?
  (lambda (l k)
    (assoc k (vector-ref result-map l))))

(define ever-reached?
  (lambda (l)
    (not (null? (vector-ref result-map l)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Variable result maps, Var x Contour -> Point.
;; Implemented as association lists distributed in Names.

(define init-var-map!
  (lambda ()
    (for-each
      (lambda (x) (set-Name-map! x '()))
      variables)))

(set-index-var-map!
  (lambda (x k)
    (let ([r (assoc k (Name-map x))])
      (if r
          (cdr r)
          (let ((v (make-empty-point x k)))
            (set-Name-map! x (cons (cons k v) (Name-map x)))
            v)))))

(define contours-at-var
  (lambda (x)
    (map car (Name-map x))))

(define points-at-var
  (lambda (x)
    (map cdr (Name-map x))))

(define values-at-var
  (lambda (x)
    (for/fold ([is (intset-make-empty)]) ([p (in-list (points-at-var x))])
      (intset-union is (point-elements p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract environments, Var -> Contour.

(set-aenv-lookup! lookup)
(define aenv-extend extend-env)
(define aenv-extend* extend-env*)
(define aenv-empty empty-env)
(define aenv-restrict env-restrict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract values are implemented as integers.
;;
;;  Closures are
;;     (kind l k env)                where kind is 'closure.
;;  Continuations are
;;     (kind l k)                    where kind is 'cont.
;;  Constructed values (cons, vec, defined things) are
;;     (kind l k field ...).
;;  Primitives are
;;     (kind l)                      where kind is 'prim.
;;  Simple values are
;;     (kind l).

(define aval-table (vector '()))
(define aval-hash-table (vector '()))
(define n-avals 0)

(define init-aval!
  (lambda ()
    (set! n-avals 0)
    (set! aval-table (make-vector n-labels #f))
    (set! aval-hash-table (make-vector n-labels '()))))

(define aval
  (lambda (kind l . args)
    (define l*
      (cond [(or (eq? Const-split #t)
              (and (pair? Const-split) (memq kind Const-split))
              (not (null? args))
              (eq? kind 'prim))
             l]
            [else 0]))
    (define key `(,kind ,@args))
    (define r (assoc key (vector-ref aval-hash-table l*)))
    (cond [r (cdr r)]
          [else
           (define v `(,kind ,l* ,@args))
           (define n n-avals)
           ;; Grow the vector if it needs space.
           (when (= n (vector-length aval-table))
             (define x
               (vector-tabulate
                (* 2 n)
                (lambda (i)
                  (if (< i n) (vector-ref aval-table i) 0))))
             (set! aval-table x))
           (vector-set! aval-table n v)
           (vector-set! aval-hash-table l*
                        (cons (cons key n)
                              (vector-ref aval-hash-table l*)))
           (set! n-avals (+ 1 n-avals))
           n])))

(set-aval-kind!    (lambda (n) (car (vector-ref aval-table n))))
(set-aval-label!   (lambda (n) (cadr (vector-ref aval-table n))))
(define aval-contour (lambda (n) (caddr (vector-ref aval-table n))))
(set-aval-env!     (lambda (n) (cadddr (vector-ref aval-table n))))
(define aval-fields  (lambda (n) (cdddr (vector-ref aval-table n))))
(define aval-is-simple? (lambda (n) (null? (cddr (vector-ref aval-table n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sets of abstract values, implemented as intsets.

;; Turn a list of avals into a set
(define list->avals list->intset)

;; See if any of several constructors are in a set of avals
(define in-avals?
  (lambda (con a)
    (intset-exists?
      (lambda (x) (memq (aval-kind x) con))
      a)))

;; See if any but certain constructors are in an abstract value set
(define except-in-avals?
  (lambda (con a)
    (intset-exists?
      (lambda (x) (not (memq (aval-kind x) con)))
      a)))

;; Filter avals for certain constructors
(define filter-avals
  (lambda (con a)
    (intset-filter
      (lambda (x) (memq (aval-kind x) con))
      a)))

;; Filter avals for all but certain constructors
(define except-avals
  (lambda (con a)
    (intset-filter
      (lambda (x) (not (memq (aval-kind x) con)))
      a)))

;; Split a set of abstract values, generating new contours for closures
(set-split!
  (lambda (a new-contour)
    (intset-map
      (lambda (v)
        (if (eq? (aval-kind v) 'closure)
            (aval 'closure
                  (aval-label v)
                  (new-contour (aval-contour v))
                  (aval-env v))
            v))
      a)))

;; Split a set of abstract values, replacing contours of closures and certain environment vars
(set-split-env!
  (lambda (a vars new-contour)
    (intset-map
      (lambda (v)
        (if (eq? (aval-kind v) 'closure)
            (aval 'closure
                  (aval-label v)
                  (new-contour (aval-contour v))
                  (env-map
                    (lambda (x k)
                      (if (memq x vars)
                          (new-contour k)
                          k))
                    (aval-env v)))
            v))
      a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Program points.
;;  label, contour - name of point
;;  new    - set of new values not yet propagated to some successors
;;  old    - set of old values that have been propagated to all successors
;;  succ   - list of procedures to be called with new values
;;
;; invariant : new does not intersect old.
;;
;; Successor actions accept an intset of new values.  Accepting several
;; values at once is important: it yields a factor of 2 in performance.

(struct Point (label
               contour
               [new #:mutable]
               [old #:mutable]
               [succ #:mutable]) #:prefab)

(set-point-elements!
  (lambda (p)
    (intset-union (Point-new p) (Point-old p))))

(define make-empty-point
  (lambda (l k)
    (set! n-points (+ 1 n-points))
    (Point
      l
      k
      (intset-make-empty)
      (intset-make-empty)
      '())))

(set-p->!
  (lambda (p action)
    (set-Point-succ! p (cons action (Point-succ p)))
    (unless (intset-empty? (Point-old p))
      (action (Point-old p)))))

(define p->p
  (lambda (p s)
    (p-> p (lambda (new) (p+avals s new)))))

(define p->1
  (lambda (p action)
    (if (or (not (intset-empty? (Point-old p)))
            (not (intset-empty? (Point-new p))))
        (action)
        (p-> p (let ([first #t])
                 (lambda (new)
                   (when first
                     (set! first #f)
                     (action))))))))

(define p+aval
  (lambda (p v)
    (unless (intset-member? v (Point-old p))
      (set-Point-new! p (intset-add v (Point-new p)))
      (enqueue-point! p))))

(set-p+avals!
  (lambda (p new)
    (let ([new (intset-difference new (Point-old p))])
      (unless (intset-empty? new)
        (set-Point-new! p (intset-union new (Point-new p)))
        (enqueue-point! p)))))

(define work-q '())

(define init-work-q!
  (lambda ()
    (set! work-q (queue-make-empty))))

(define enqueue-point!
  (lambda (p)
    (unless (queue-memq p work-q)
      (queue-push! p work-q))))

(define propagate-across-edges!
  (lambda ()
    (let loop ()
      (unless (zero? (queue-size work-q))
        (define p (queue-pop! work-q))
        (define new (Point-new p))
        (set-Point-old! p (intset-union (Point-old p) new))
        (set-Point-new! p (intset-make-empty))
        (for ([succ (in-list (Point-succ p))]) (succ new))
        (loop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Printing

(define print-aval
  (let ((penv (match-lambda [(cons n k) `(,(Name-name n) -> ,k)])))
    (lambda (x)
      (define kind (aval-kind x))
      (define l (aval-label x))
      (cond [(aval-is-simple? x)
             `(,kind ,l)]
            [(memq kind '(closure))
             `(,kind ,l
                     ,(print-contour (aval-contour x))
                     ,(map penv (aval-env x)))]
            [else
             `(,kind ,l
                     ,(print-contour (aval-contour x))
                     ,@(for/list ([f (in-list (aval-fields x))])
                         (define l (Point-label f))
                         (cons (cond [(Name? l) (Name-name l)]
                                     [else l])
                               (Point-contour f))))]))))

(define print-point
  (lambda (a)
    (map print-aval a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statistics

(define n-points 0)

(set-print-abstract-statistics!!
  (lambda ()
    (define size (lambda (p) (intset-size (point-elements p))))
    (define n (+ (for*/sum ([v (in-list variables)]
                            [p (in-list (points-at-var v))])
                           (size p))
                 (for*/sum ([l (in-range n-labels)]
                            [p (in-list (points-at-label l))])
                           (size p))))
    (printf "; ~a program points, ~a distinct values, ~a values in the graph~%"
            n-points n-avals n)
    (printf "; ~a entries in call map~%" (total-call-map-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ALL OLD AND POSSIBLY OUT OF DATE

(define unioning-time (vector 0))
(define merging-time 0)
(define union-clock 0)
(define union-sub-clock 0)
(define union-clock-granularity 100)
(define union-counts `(0))

(define init-abstract-statistics!
  (lambda ()
    (set! merging-time 0)
    (set! union-clock 0)
    (set! union-sub-clock 0)
    (set! unioning-time (make-vector (* 2 n-labels) 0))
    (set! union-counts `(0))
    (void)))

(define reinit-abstract-statistics!
  (lambda ()
    (set! union-counts (cons 0 (cons -10 union-counts)))))

(define stats
  (lambda ()
    (let ((now (current-inexact-milliseconds)))
      (printf "~a distinct avals have been constructed.~%" n-avals)
      (printf "Result map has ~a labels, ~a variables.~%"
        n-labels
        (length variables))
      (let* ((full-map (append
                         (map Name-map variables)
                         (vector->list result-map)))
             (n-points (foldl-map + length 0 full-map))
             (n-vals (foldl-map
                       +
                       (lambda (y)
                         (foldl-map
                           +
                           (lambda (x) (intset-size (point-elements (cdr x))))
                           0
                           y))
                       0
                       full-map)))
        (printf "Result map has ~a Points containing ~a values.~%"
          n-points
          n-vals))
      (printf "Merging time ~a ms.~%" merging-time)
      (if (zero? running-time)
          (begin
            (printf "Running time ~a ms (so far).~%" (- now starting-time))
            (set-starting-time! (+ starting-time (- (current-inexact-milliseconds) now))))
          (printf "Running time ~a ms.~%" running-time))
      (void))))

(define print-points
  (lambda ()
    (let* ((full-map (append
                       (map Name-map variables)
                       (vector->list result-map)))
           (n-points (foldl-map + length 0 full-map))
           (n-vals (foldl-map
                     +
                     (lambda (y)
                       (foldl-map
                         +
                         (lambda (x) (intset-size (point-elements (cdr x))))
                         0
                         y))
                     0
                     full-map)))
      (printf "Result map has ~a Points containing ~a values.~%"
        n-points
        n-vals)
      (printf "Point size distribution:  (size : # of sets)~%")
      (pretty-print
        (frequency
          (lambda (mark)
            (for-each
              (lambda (y)
                (for-each
                  (lambda (x)
                    (mark (intset-size (point-elements (cdr x)))))
                  y))
              full-map))
          n-points)))))

(define report-unreachability
  (lambda ()
    (let ([apps '()])
      (natural-for-each
        (lambda (l)
          (match (label->node l)
            [(E: (App f args))
             (for-each
               (lambda (k)
                 (unless (and (reached? (labelof f) k)
                              (not (intset-empty? (point-elements (index-result-map (labelof f) k)))))
                   (set! apps (cons (cons l k) apps))))
               (contours-at-label l))]
            [_ #f]))
        n-labels)
      apps)))

(define distribution
  (lambda (dist)
    (pretty-print
      (let loop ((n (- (length dist) 1)) (acc '()))
        (cond ((> 0 n) acc)
              ((zero? (list-ref dist n)) (loop (- n 1) acc))
              (else (loop (- n 1) (cons `(,n : ,(list-ref dist n)) acc))))))))

(define (max-list lst)
  (for/fold ([acc 0]) ([x (in-list lst)])
    (max acc x)))

(define h-union-counts
  (lambda ()
    (define counts (reverse union-counts))
    (define max-count (max-list counts))
    (histogram
     (map (lambda (x)
            (if (negative? x)
                (- max-count)
                x))
          counts))))

(define histogram
  (lambda (dist)
    (let* ((counts (foldr
                     (lambda (x acc)
                       (if (and (null? acc) (zero? x))
                           '()
                           (cons x acc)))
                     '()
                     dist))
           (max-count (max-list counts)))
      (printf "X-axis 0:~a, Y-axis 0:~a~n" (length counts) max-count)
      (make-histogram
        intset-version
        max-count
        counts))))

(define frequency
  (lambda (enumerate bound)
    (let ((dist (make-vector bound 0)))
      (enumerate
        (lambda (n) (vector-set! dist n (+ 1 (vector-ref dist n)))))
      (let loop ((n (- bound 1)) (acc '()))
        (cond ((> 0 n) acc)
              ((zero? (vector-ref dist n)) (loop (- n 1) acc))
              (else (loop (- n 1) (cons `(,n : ,(vector-ref dist n)) acc))))))))
