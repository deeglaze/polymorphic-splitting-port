#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Find strongly connected components of definitions.

(require "library.rkt"
         "data.rkt"
         "free.rkt"
         "graph-ops.rkt"
         racket/mpair)
(provide make-components! find-define)

(define find-define
  (lambda (x defs)
    (cond [(null? defs) #f]
          [(eq? x (Define-name (car defs))) (car defs)]
          [else (find-define x (cdr defs))])))

(define (mmap/list f lst)
  (match lst
    ['() '()]
    [(list a) (mlist (f a))]
    [(cons a d)
     (define res (mlist (f a)))
     (let loop ([d d] [last res])
       (match d
         ['() res]
         [(cons a d)
          (define nlast (mlist (f a)))
          (set-mcdr! last nlast)
          (loop d nlast)]))]))

(define make-components!
  (lambda (defs)
    (define (name->define x) (find-define x defs))
    (define names (map Define-name defs))
    (define (ref-of x)
      (list->mlist
       (intersect2 names (free-in-exp (Define-exp (name->define x))))))
    (define comps (scc (list->mlist names) ref-of))

    (for* ([c (in-mlist comps)]
           [name (in-mlist c)])
      (set-Name-component! name (mlist->list c)))))
