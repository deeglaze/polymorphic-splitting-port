#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The call map, Label -> (set Label).
;; Maps lambda's and primitives to the sites where they may be called.
;; Implemented as a vector of sets.

(require "library.rkt"
         "mutrec.rkt")
(provide call-map init-call-map!
         index-call-map extend-call-map!
         total-call-map-size)

(define call-map (vector empty-set))

(define init-call-map!
  (lambda ()
    (set! call-map (make-vector n-labels empty-set))))

(define index-call-map
  (lambda (l)
    (vector-ref call-map l)))

(define extend-call-map!
  (lambda (l call-site)
    (vector-set! call-map l
      (union2 (vector-ref call-map l) (set call-site)))))

(define total-call-map-size
  (lambda ()
    (natural-foldl
      (lambda (sum l)
        (+ sum (length (index-call-map l))))
      0
      n-labels)))
