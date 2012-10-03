#lang scheme/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Misc useful functions

(require ;; also srfi/1
         (only-in racket/list flatten filter-map take last)
         (only-in racket/base filter)
         (only-in srfi/1 list-index list-tabulate)
         ;; also srfi/43
         (only-in racket/vector vector-map vector-append)
         (only-in srfi/43 vector-for-each)
         racket/match)
(provide set-vector!
         set-string!
         ;; known list functions
         flatten
         foldr ormap andmap list-index filter filter-map
         (rename-out [take sublist]
                     [last rac]
                     [map mapLR]
                     [list-tabulate tabulate])
         ;; rolled list functions
         mapRL foldl1 foldr1 foldr-map foldl-map
         rdc map-with-n
         natural-foldl natural-map iota
         ;; known vector functions
         vector-for-each vector-map vector-append
         ;; rolled vector functions
         vector-foldl vector-foldr vector-tabulate
         set-vector!
         ;; imperative functions
         natural-for-each set-string!
         ;; set implementation
         empty-set empty-set? set list->set cardinality element-of?
         set<= set-eq?         
         union2 union
         setdiff2 setdiff
         intersect2 intersect
         ;; others
         readfile repeated generate-counter symbol-append
         memo memo-hashed memo* memo-rec)

(define set-vector! vector-set!)
(define set-string! string-set!)

(define symbol-append
  (λ args (string->symbol (apply string-append (map symbol->string args)))))
;; Map from right to left.
(define mapRL
  (lambda (f l)
    (match l
      ['() '()]
      [(cons x y) (let ((v (mapRL f y))) (cons (f x) v))])))

;; The foldl in this old code has swapped arguments to the function
(define foldl
  (λ (f b l)
     (for/fold ([acc b]) ([x (in-list l)])
       (f acc x))))

;; Fold a binary function down a non-empty list, left to right.
;; (left operand of f is accumulator)
(define foldl1
  (lambda (f l)
    (let loop ([l (cdr l)]
               [acc (car l)])
      (if (null? l)
          acc
          (loop (cdr l) (f acc (car l)))))))

;; Fold a binary function down a non-empty list, right to left.
;; (right operand of f is accumulator)
(define foldr1
  (lambda (f l)
    (if (null? (cdr l))
        (car l)
        (f (car l) (foldr1 f (cdr l))))))

;; Foldl composed appropriately with map
(define foldl-map
  (lambda (foldf mapf i l)
    (if (pair? l)
        (foldl-map foldf mapf (foldf i (mapf (car l))) (cdr l))
        i)))

;; Foldr composed appropriately with map
(define foldr-map
  (lambda (foldf mapf i l)
    (if (pair? l)
        (foldf (mapf (car l)) (foldr-map foldf mapf i (cdr l)))
        i)))

;; All but the last element of a list.
(define rdc
  (match-lambda
    [(list _) '()]
    [(cons x rest) (cons x (rdc rest))]))

;; Map left to right, but also pass f a 0-based index.
(define map-with-n
  (lambda (f l)
    (let loop ([l l]
               [n 0])
      (match l
        ['() '()]
        [(cons x y) (let ((v (f x n))) (cons v (loop y (+ 1 n))))]))))

;; Return a list of the s-expressions in a file.
(define readfile
  (lambda (f)
    (letrec ((rf (lambda ()
                   (let ((sexp (read)))
                     (if (eof-object? sexp)
                         '()
                         (cons sexp (rf)))))))
      (with-input-from-file f rf))))

;; Find a repeated element in a list
(define repeated
  (lambda (l)
    (cond [(null? l) #f]
          [(memq (car l) (cdr l)) (car l)]
          [else (repeated (cdr l))])))

;; Build a thunk that counts up from an initial value.
(define generate-counter
  (lambda (n)
    (lambda ()
      (let ([m n])
        (set! n (+ 1 n))
        m))))

;; Memoize a function, using equal? to compare args
(define memo
  (lambda (f)
    (let ((q '()))
      (lambda args
        (let ((r (assoc args q)))
          (if r
              (cdr r)
              (let ((v (apply f args)))
                (set! q (cons (cons args v) q))
                v)))))))

;; Memoize a function, using equal? on hashed args
(define memo-hashed
  (lambda (f hash)
    (let ((q '()))
      (lambda args
        (let* ((h (hash args))
               (r (assoc h q)))
          (if r
              (cdr r)
              (let ((v (apply f args)))
                (set! q (cons (cons h v) q))
                v)))))))

;; Memoize a function, passing comparison function
(define memo*
  (lambda (f compare)
    (let ((q '()))
      (lambda args
        (let loop ((s q))
          (cond [(null? s)
                 (let ((v (apply f args)))
                   (set! q (cons (cons args v) q))
                   v)]
                [(compare args (caar s))
                 (cdar s)]
                [else
                 (loop (cdr s))]))))))

;; Memoize a recursive function that returns no interesting result,
;; passing a comparison function
(define memo-rec
  (lambda (f compare)
    (let ((q '()))
      (lambda args
        (let loop ((s q))
          (cond [(null? s)
                 (set! q (cons args q))
                 (apply f args)
                 (void)]
                [(compare args (car s))
                 (void)]
                [else
                 (loop (cdr s))]))))))

;; Create a new vector from a function.
(define vector-tabulate
  (lambda (size f)
    (if (zero? size)
        (vector)
        (let ((x (make-vector size (f 0))))
          (let loop ((i 1))
            (when (< i size)
              (vector-set! x i (f i))
              (loop (+ i 1))))
          x))))

;; Foldl for vectors
(define vector-foldl
  (lambda (f i v)
    (let ([n (vector-length v)])
      (let loop ([j 0] [acc i])
        (if (< j n)
            (loop (+ j 1) (f acc (vector-ref v j)))
            acc)))))

;; Foldr for vectors
(define vector-foldr
  (lambda (f i v)
    (let ([n (vector-length v)])
      (let loop ([j (- n 1)] [acc i])
        (if (<= 0 j)
            (loop (- j 1) (f (vector-ref v j) acc))
            acc)))))

;; For-each over the integers 0 .. n-1
(define natural-for-each
  (lambda (f n) (for ([i (in-range n)]) (f i))))

;; Map over the integers 0 .. n-1
(define natural-map (lambda (f n) (build-list n f)))

;; Fold left over the integers 0 .. n-1
(define natural-foldl
  (lambda (f i n)
    (let loop ((j 0) (acc i))
      (if (< j n)
          (loop (+ j 1) (f acc j))
          acc))))

;; Build a list of length n, with optional values for elements
(define iota
  (lambda (n . val)
    (let loop ((n n) (acc '()))
      (if (< 0 n)
          (loop (- n 1)
                (cons (if (null? val) (- n 1) (car val)) acc))
          acc))))

;; Format a number into a simple decimal
;; d - number of digits after the decimal point
;; w - minimum with of number in characters
(define (format-num d w num)
  (let* ((expt-10-d (expt 10 d))
         (n (floor (inexact->exact (round (* (abs num) expt-10-d)))))
         (i (quotient n expt-10-d))
         (f (modulo n expt-10-d))
         (si (string-append
               (if (< num 0) "-" "")
               (number->string i 10)))
         (sf (number->string (+ f expt-10-d) 10))
         (sf (if (> d 0)
                 (string-append "." (substring sf 1 (string-length sf)))
                 ""))
         (lsi (string-length si))
         (lsf (string-length sf))
         (blanks (- w (+ lsi lsf))))
    (string-append (make-string (max blanks 0) #\space) si sf)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Set operations implemented by lists.
;; Identity of elements is based on eq?.
;; These should probably be sped up some day.

(define empty-set '())

(define empty-set? null?)

;; construct a set
(define set
  (lambda l
    (list->set l)))

;; construct a set from a list by removing duplicates
(define list->set
  (match-lambda
    ['() '()]
    [(cons x y) (if (memq x y)
                    (list->set y)
                    (cons x (list->set y)))]))

;; test for membership
(define element-of?
  (lambda (x set)
    (and (memq x set) #t)))

(define cardinality length)

;; does s2 contain s1?
(define set<=
  (lambda (a b)
    (andmap (lambda (x) (memq x b)) a)))

;; are two sets equal? (mutually containing)
(define set-eq?
  (lambda (a b)
    (and (= (cardinality a) (cardinality b)) (set<= a b))))

;; unite two sets
(define union2
  (lambda (a b)
    (if (null? b)
        a
        (foldr (lambda (x b)
                 (if (memq x b)
                     b
                     (cons x b)))
          b
          a))))

;; unite any number of sets
(define union
  (lambda l
    (foldl union2 '() l)))

;; take set b from set a
(define setdiff2
  (lambda (a b)
    (if (null? b)
        a
        (foldl (lambda (c x)
                 (if (memq x b)
                     c
                     (cons x c)))
          '()
          a))))

;; take 2nd and other sets from first set
(define setdiff
  (lambda l
    (if (null? l)
        '()
        (setdiff2 (car l) (foldl union2 '() (cdr l))))))

;; intersect two sets
(define intersect2
  (lambda (a b)
    (if (null? b)
        '()
        (foldl (lambda (c x)
                 (if (memq x b)
                     (cons x c)
                     c))
          '()
          a))))

;; intersect several sets
(define intersect
  (lambda l
    (if (null? l)
        '()
        (foldl intersect2 (car l) l))))
