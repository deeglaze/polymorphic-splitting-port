#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Given a list of definitions, mark definitions whose value may
;; be used before it is defined.

(require "library.rkt"
         "data.rkt"
         "free.rkt"
         "graph-ops.rkt"
         "components.rkt"
         "mutrec.rkt")
(provide mark-used-before-defined!)

(define mark-used-before-defined!
  (lambda (defs)
    (let* ([defs (filter Define? defs)]
           [name->define (lambda (x) (find-define x defs))]
           [names (map Define-name defs)]
           [ref-of (lambda (x) (intersect2 names (free-in-exp (Define-exp (name->define x)))))]
           [ref-of* (transitive names ref-of)])
      (letrec ([active?
                (match-lambda
                  [(E: (or (? Lam?) (? Vlam?) (? Const?)))
                   #f]
                  [(Define _ exp)
                   (active? exp)]
                  [(E: (Var x))
                   (memq x names)]
                  [(E: (or (And exps) (Or exps) (Begin exps)))
                   (ormap active? exps)]
                  [(E: (If test then els))
                   (or (active? test) (active? then) (active? els))]
                  [(E: (or (Let bindings body) (Letr bindings body)))
                   (or (ormap active? bindings) (active? body))]
                  [(E: (Set! _ exp))
                   (active? exp)]
                  [e #t])])
        (let loop ([defs defs] [names names])
          (match defs
            [(cons (Define x e) rest)
             (when (active? e)
               (for-each
                 (lambda (y)
                   (unless (Name-used-before-defined? y)
                     (printf "Note: ~a might be used by ~a before being bound~%"
                       (pname* y) (pname* x))
                     (set-Name-used-before-defined?! y #t)))
                 (intersect2 (ref-of* x) names)))
             (loop rest (cdr names))]
            ['() #f]))))))
