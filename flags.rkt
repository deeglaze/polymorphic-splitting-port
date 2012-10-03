#lang racket

(provide If-split Const-split set-Const-split! set-If-split!
         limited-pretty-print clock-granularity)

;; Flags controlling if splitting and constant splitting
(define If-split #t)
(define Const-split #f)

(define (set-If-split! v) (set! If-split v))
(define (set-Const-split! v) (set! Const-split v))

(define limited-pretty-print
  (lambda (obj depth)
    (parameterize ([pretty-print-depth depth])
      (pretty-print obj))))

(define clock-granularity 1/1000)
