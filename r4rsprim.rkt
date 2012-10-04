#lang racket

(require (only-in "macros.rkt" special))
(provide r4rs-prims primitives-to-rename)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-primitive primitives.

;; At present these cannot refer to each other.

(define r4rs-prims
  `((define caar (lambda (x) (car (car x))))
    (define cadr (lambda (x) (car (cdr x))))
    (define cdar (lambda (x) (cdr (car x))))
    (define cddr (lambda (x) (cdr (cdr x))))
    (define caaar (lambda (x) (car (car (car x)))))
    (define caadr (lambda (x) (car (car (cdr x)))))
    (define cadar (lambda (x) (car (cdr (car x)))))
    (define caddr (lambda (x) (car (cdr (cdr x)))))
    (define cdaar (lambda (x) (cdr (car (car x)))))
    (define cdadr (lambda (x) (cdr (car (cdr x)))))
    (define cddar (lambda (x) (cdr (cdr (car x)))))
    (define cdddr (lambda (x) (cdr (cdr (cdr x)))))
    (define caaaar (lambda (x) (car (car (car (car x))))))
    (define caaadr (lambda (x) (car (car (car (cdr x))))))
    (define caadar (lambda (x) (car (car (cdr (car x))))))
    (define caaddr (lambda (x) (car (car (cdr (cdr x))))))
    (define cadaar (lambda (x) (car (cdr (car (car x))))))
    (define cadadr (lambda (x) (car (cdr (car (cdr x))))))
    (define caddar (lambda (x) (car (cdr (cdr (car x))))))
    (define cadddr (lambda (x) (car (cdr (cdr (cdr x))))))
    (define cdaaar (lambda (x) (cdr (car (car (car x))))))
    (define cdaadr (lambda (x) (cdr (car (car (cdr x))))))
    (define cdadar (lambda (x) (cdr (car (cdr (car x))))))
    (define cdaddr (lambda (x) (cdr (car (cdr (cdr x))))))
    (define cddaar (lambda (x) (cdr (cdr (car (car x))))))
    (define cddadr (lambda (x) (cdr (cdr (car (cdr x))))))
    (define cdddar (lambda (x) (cdr (cdr (cdr (car x))))))
    (define cddddr (lambda (x) (cdr (cdr (cdr (cdr x))))))
    (define list (lambda a a))
    (define length
      (lambda (a)
        (recur loop ((a a) (len 0))
          (if (null? a)
              len
              (loop (cdr a) (+ 1 len))))))
    (define append
      (lambda a
        (letrec ((app2 (lambda (a b)
                         (if (null? a)
                             b
                             (cons (car a) (app2 (cdr a) b))))))
          (recur loop ((a a))
            (cond ((null? a) '())
                  ((null? (cdr a)) (car a))
                  (else (app2 (car a) (loop (cdr a)))))))))
    (define reverse
      (lambda (a)
        (recur loop ((a a) (acc '()))
          (if (null? a)
              acc
              (loop (cdr a) (cons (car a) acc))))))
    (define list-tail
      (lambda (a n)
        (if (zero? n)
            a
            (list-tail (cdr a) (- n 1)))))
    (define list-ref
      (lambda (a n)
        (if (zero? n)
            (car a)
            (list-ref (cdr a) (- n 1)))))
    (define memq
      (lambda (x a)
        (cond ((null? a) #f)
              ((eq? x (car a)) a)
              (else (memq x (cdr a))))))
    (define memv
      (lambda (x a)
        (cond ((null? a) #f)
              ((eqv? x (car a)) a)
              (else (memv x (cdr a))))))
    (define member
      (lambda (x a)
        (cond ((null? a) #f)
              ((equal? x (car a)) a)
              (else (member x (cdr a))))))
    (define assq
      (lambda (x a)
        (cond ((null? a) #f)
              ((eq? x (car (car a))) (car a))
              (else (assq x (cdr a))))))
    (define assv
      (lambda (x a)
        (cond ((null? a) #f)
              ((eqv? x (car (car a))) (car a))
              (else (assv x (cdr a))))))
    (define assoc
      (lambda (x a)
        (cond ((null? a) #f)
              ((equal? x (car (car a))) (car a))
              (else (assoc x (cdr a))))))
    (define string->list
      (lambda (s)
        (recur loop ((n (- (string-length s) 1)) (acc '()))
          (if (negative? n)
              acc
              (loop (- n 1) (cons (string-ref s n) acc))))))
;    (define list->string
;      (lambda (a)
;        (apply string a)))
    (define list->string
      (lambda (a)
        (define length
          (lambda (a)
            (recur loop ((a a) (len 0))
              (if (null? a)
                  len
                  (loop (cdr a) (+ 1 len))))))
        (let ((s (make-string (length a))))
          (recur loop ((i 0) (a a))
            (if (null? a)
                s
                (begin
                  (string-set! s i (car a))
                  (loop (+ 1 i) (cdr a))))))))
    (define vector->list
      (lambda (v)
        (recur loop ((n (- (vector-length v) 1)) (acc '()))
          (if (negative? n)
              acc
              (loop (- n 1) (cons (vector-ref v n) acc))))))
;    (define list->vector
;      (lambda (a)
;        (apply vector a)))
    (define list->vector
      (lambda (a)
        (define length
          (lambda (a)
            (recur loop ((a a) (len 0))
              (if (null? a)
                  len
                  (loop (cdr a) (+ 1 len))))))
        (if (null? a)
            (vector)
            (let ((v (make-vector (length a) (car a))))
              (recur loop ((i 1) (a (cdr a)))
                (if (null? a)
                    v
                    (begin
                      (vector-set! v i (car a))
                      (loop (+ 1 i) (cdr a)))))))))
    (define map
      (lambda (f a . args)
        (letrec ((map1 (lambda (f l)
                         (if (null? l)
                             '()
                             (cons (f (car l))
                                   (map1 f (cdr l))))))
                 (map2 (lambda (f l1 l2)
                         (cond ((null? l1)
                                '())
                               ((null? l2)
                                (error 'map "lists differ in length"))
                               (else
                                 (cons (f (car l1) (car l2))
                                       (map2 f (cdr l1) (cdr l2)))))))
                 (map* (lambda (f l*)
                         (if (null? (car l*))
                             '()
                             (cons (let ((l (map1 car l*)))
                                     (if (null? l)
                                         (f)
                                         ((,special internal-apply) f l)))
                                   (map* f (map1 cdr l*)))))))
          (cond ((null? args)
                 (map1 f a))
                ((null? (cdr args))
                 (map2 f a (car args)))
                (else
                  (map* f (cons a args)))))))
    (define for-each
      (lambda (f a . args)
        (letrec ((map (lambda (f l)
                         (if (null? l)
                             '()
                             (cons (f (car l))
                                   (map f (cdr l)))))))
          (letrec ((for-each1 (lambda (f l)
                                (if (null? l)
                                    (void)
                                    (begin
                                      (f (car l))
                                      (for-each1 f (cdr l))))))
                   (for-each2 (lambda (f l1 l2)
                                (cond ((null? l1)
                                       (void))
                                      ((null? l2)
                                       (error 'for-each "lists differ in length"))
                                      (else
                                        (f (car l1) (car l2))
                                        (for-each2 f (cdr l1) (cdr l2))))))
                   (for-each* (lambda (f l*)
                                (if (null? (car l*))
                                    (void)
                                    (begin
                                      (let ((l (map car l*)))
                                        (if (null? l)
                                            (f)
                                            ((,special internal-apply) f l)))
                                      (for-each* f (map cdr l*)))))))
            (cond ((null? args)
                   (for-each1 f a))
                  ((null? (cdr args))
                   (for-each2 f a (car args)))
                  (else
                    (for-each* f (cons a args))))))))
    (define call-with-current-continuation
      (lambda (f)
        (letcc x (f x))))
    (define call-with-input-file
      (lambda (s f)
        (let* ((p (open-input-file s))
               (v (f p)))
          (close-input-port p)
          v)))
    (define call-with-output-file
      (lambda (s f)
        (let* ((p (open-output-file s))
               (v (f p)))
          (close-output-port p)
          v)))
    (define with-input-from-file
      (lambda (s f)
        ; no way to switch current input in R4RS Scheme
        (error 'with-input-from-file "not supported")
        (f)))
    (define with-output-to-file
      (lambda (s f)
        ; no way to switch current output in R4RS Scheme
        (error 'with-output-to-file "not supported")
        (f)))
    (define apply
      (lambda (f arg0 . args)
        (define list-copy
          (lambda (l)
            (if (null? l)
                '()
                (cons (car l) (list-copy (cdr l))))))
        (define flatten
          (lambda (args)
            (if (null? (cdr args))
                (car args)
                (cons (car args) (flatten (cdr args))))))
        (let ((m (flatten (cons arg0 args))))
          (cond ((null? m) (f))
                ((null? (cdr m)) (f (car m)))
                ((null? (cdr (cdr m))) (f (car m) (car (cdr m))))
                (else (let ((n (list-copy m)))
                        (if (null? n)
                            (error 'apply "can't happen")
                            ((,special internal-apply) f n))))))))
    (define make-promise
      (lambda (thunk)
        (let ([first #t]
              [val #f])
          (lambda ()
            (cond [(eq? first 'forcing) (error 'force "recursive force")]
                  [first (set! first 'forcing)
                         (set! val (thunk))
                         (set! first #f)
                         val]
                  [else val])))))
    (define force (lambda (promise) (promise)))
    (define make-list
      (lambda (n val)
        (recur loop ((n n))
          (if (< n 1)
              '()
              (cons val (loop (- n 1)))))))
    (define andmap
      (lambda (f list0 . lists)
        (if (null? list0)
            (and)
            (recur loop ((lists (cons list0 lists)))
              (if (null? (cdr (car lists)))
                  (apply f (map car lists))
                  (and (apply f (map car lists))
                       (loop (map cdr lists))))))))
    (define ormap
      (lambda (f list0 . lists)
        (if (null? list0)
            (or)
            (recur loop ((lists (cons list0 lists)))
              (if (null? (cdr (car lists)))
                  (apply f (map car lists))
                  (or (apply f (map car lists))
                      (loop (map cdr lists))))))))
    (define call/cc
      (lambda (f)
        (letcc x (f x))))
    (define dynamic-wind
      (lambda (in doit out)
        (let* ([a (in)]
               [b (doit)]
               [c (out)])
          b)))
    (define sort
      (lambda (compare in)
        in))
    ))

(define primitives-to-rename
  (append
    (map cadr r4rs-prims)
    '(reverse! append! add1 sub1 vector-copy sort sort! reset pretty-print random)))
