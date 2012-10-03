#lang racket

(require "library.rkt")
(provide format-number)
;; Quick hack code not guaranteed to be highly accurate.
;; pad a number to left digits before the decimal point,
;; right zeros after

(define format-number
  (lambda (n left right)
    (let* ((decimal (floor (abs n)))
           (before (if (zero? decimal)
                       (list #\0)
                       (reverse
                         (let loop ((d decimal))
                           (if (zero? d)
                               '()
                               (cons (digit->char (modulo d 10))
                                     (loop (quotient d 10))))))))
           (before (append
                     (iota (- left (length before)) #\space)
                     (if (negative? n) (cons #\- before) before)))
           (fraction (- (abs n) decimal))
           (after (let loop ((f fraction) (k right))
                    (if (>= 0 k)
                        '()
                        (cons (digit->char (floor (* f 10)))
                              (loop (- (* f 10) (floor (* f 10))) (- k 1)))))))
      (list->string (append before (list #\.) after)))))

(define digit->char
  (lambda (n)
    (case n
      ((0) #\0)
      ((1) #\1)
      ((2) #\2)
      ((3) #\3)
      ((4) #\4)
      ((5) #\5)
      ((6) #\6)
      ((7) #\7)
      ((8) #\8)
      ((9) #\9))))
