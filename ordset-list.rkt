#lang racket

(provide ordset
         (struct-out order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Set operations for elements with a total order.
;;
;; Implemented as ordered lists.

(struct order
        (version make-empty empty? size set add member? exists?
         for-each map foldl foldr filter singleton
         set->list list->set
         union min max difference intersection delete
         subset? union-and-note equal?) #:prefab)

(define ordset
  (lambda (< =)

    (define version "ordered lists")

    (define ordset-make-empty (lambda () '()))

    (define ordset-size length)

    (define ordset
      (lambda vals
        (for/fold ([s '()])
            ([x (in-list vals)])
          (ordset-add x s))))

    (define ordset-add
      (lambda (x s0)
        (let loop ([s s0]
                   [before '()])
          (cond [(or (null? s) (< x (car s)))
                 (let loop2 ((s (cons x s)) (before before))
                   (if (null? before)
                       s
                       (loop2 (cons (car before) s) (cdr before))))]
                [(= x (car s))
                 s0]
                [else
                 (loop (cdr s) (cons (car s) before))]))))

    (define ordset-exists?
      (lambda (p s)
        (and (pair? s)
             (or (p (car s)) (ordset-exists? p (cdr s))))))

    (define ordset-map
      (lambda (f s)
        (list->ordset (map f s))))

    (define ordset-singleton
      (lambda (x)
        (list x)))

    (define ordset->list (lambda (x) x))

    (define list->ordset
      (lambda (l)
        (for/fold ([s '()]) ([x (in-list l)]) (ordset-add x s))))

    ;; This operation tries to share as much of s1 as possible.
    (define ordset-union
      (lambda (s1 s2)
        (let loop ([s1 s1] [s2 s2])
          (match* (s1 s2)
            [((== s2 eq?) _) s1]
            [(_ '()) s1]
            [('() _) s2]
            [((cons s1a s1d) (cons s2a s2d))
             (cond [(< s1a s2a)
                    (match (loop s1d s2)
                      [(== s2d eq?) s1]
                      [x (cons s1a x)])]
                   [(= s1a s2a)
                    (match (loop s1d s2d)
                      [(== s2d eq?) s1]
                      [x (cons s1a x)])]
                   [else (cons s2a (loop s1 s2d))])]
            [(_ _) (error 'ordset-union "Expected lists ~a ~a" s1 s2)]))))

    ;; This operation tries to share as much of s1 as possible.
    ;; It notes things that are in s2 but not in s1.
    (define ordset-union-and-note
      (lambda (s1 s2 note)
        (let loop ((s1 s1) (s2 s2))
          (cond ((or (eq? s1 s2) (null? s2)) s1)
                ((null? s1)
                 (for-each note s2)
                 s2)
                ((< (car s1) (car s2))
                 (let ((x (loop (cdr s1) s2)))
                   (if (eq? x (cdr s1))
                       s1
                       (cons (car s1) x))))
                ((= (car s1) (car s2))
                 (let ((x (loop (cdr s1) (cdr s2))))
                   (if (eq? x (cdr s1))
                       s1
                       (cons (car s1) x))))
                (else
                  (note (car s2))
                  (cons (car s2) (loop s1 (cdr s2))))))))

    ;; This operation tries to share as much of s2 as possible.
    ;; It notes things that are in s2 but not in s1.
    (define ordset-union-and-note2
      (lambda (s1 s2 note)
        (let loop ((s1 s1) (s2 s2))
          (cond ((eq? s1 s2)
                 s2)
                ((null? s1)
                 (for-each note s2)
                 s2)
                ((null? s2)
                 s1)
                ((< (car s1) (car s2))
                 (cons (car s1) (loop (cdr s1) s2)))
                ((= (car s1) (car s2))
                 (let ((x (loop (cdr s1) (cdr s2))))
                   (if (eq? x (cdr s2))
                       s2
                       (cons (car s2) x))))
                (else
                  (note (car s2))
                  (let ((x (loop s1 (cdr s2))))
                    (if (eq? x (cdr s2))
                        s2
                        (cons (car s2) x))))))))

    (define ordset-difference
      (lambda (s1 s2)
        (cond ((or (null? s1) (null? s2))
               s1)
              ((< (car s1) (car s2))
               (cons (car s1) (ordset-difference (cdr s1) s2)))
              ((= (car s1) (car s2))
               (ordset-difference (cdr s1) (cdr s2)))
              (else
                (ordset-difference s1 (cdr s2))))))

    (define ordset-intersection
      (lambda (s1 s2)
        (cond ((or (null? s1) (null? s2))
               '())
              ((= (car s1) (car s2))
               (cons (car s1) (ordset-intersection (cdr s1) (cdr s2))))
              ((< (car s1) (car s2))
               (ordset-intersection (cdr s1) s2))
              (else
                (ordset-intersection s1 (cdr s2))))))

    (define ordset-delete
      (lambda (x s0)
        (if (member x s0)
            (let loop ((s s0))
              (cond ((null? s) '())
                    ((eq? x (car s)) (cdr s))
                    (else (cons (car s) (loop (cdr s))))))
            s0)))

    (define ordset-subset?
      (lambda (s1 s2)
        (cond ((null? s1)
               #t)
              ((null? s2)
               #f)
              ((< (car s1) (car s2))
               #f)
              ((= (car s1) (car s2))
               (ordset-subset? (cdr s1) (cdr s2)))
              (else
               (ordset-subset? s1 (cdr s2))))))

    (define ordset-min
      (lambda (s)
        (if (null? s)
            (error 'ordset-min "min of empty set")
            (car s))))

    (define ordset-max
      (lambda (s)
        (if (null? s)
            (error 'ordset-max "max of empty set")
            (let loop ([s s])
              (if (null? (cdr s))
                  (car s)
                  (loop (cdr s)))))))

    (order version ordset-make-empty null? ordset-size ordset ordset-add member 
           ordset-exists? for-each ordset-map foldl foldr filter ordset-singleton
           ordset->list list->ordset ordset-union ordset-min ordset-max ordset-difference
           ordset-intersection ordset-delete ordset-subset? ordset-union-and-note equal?)))
