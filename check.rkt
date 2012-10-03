#lang racket

(require "library.rkt"
         "intset.rkt"
         "data.rkt"
         "mutrec.rkt"
         "unparse.rkt")

(provide insert-runtime-checks check-summary check-output)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Marking checks in the tree.

(define check-map (intset-make-empty))

(define init-check-map!
  (lambda ()
    (set! check-map (intset-make-empty))))

(set-check-needed?!
  (lambda (l)
    (intset-member? l check-map)))

(define insert-check!
  (lambda (l)
    (set! check-map (intset-add l check-map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inserting Runtime checks

(define insert-runtime-checks
  (lambda ()
    (init-check-map!)
    (natural-for-each
      (lambda (l)
        (match (label->node l)
          [(E: (App fun args))
           (let ([nargs (length args)]
                 [fl (labelof fun)])
             (for-each
               (lambda (k)
                 (intset-for-each
                   (lambda (a)
                     (case (aval-kind a)
                       [(closure)
                        (match (label->node (aval-label a))
                          [(E: (Lam: required _))
                           (unless (= nargs (length required))
                             (insert-check! (aval-label a)))]
                          [(E: (Vlam: required _ _))
                           (unless (>= nargs (length required))
                             (insert-check! (aval-label a)))])]
                       [(cont)
                        (unless (= 1 nargs)
                          (insert-check! (aval-label a)))]
                       [(prim)
                        (match-let ([(E: (Var p)) (label->node (aval-label a))])
                          (unless (prim-applies-to?
                                    p
                                    (map (lambda (arg)
                                           (index-result-map (labelof arg) k))
                                         args))
                            (insert-check! (aval-label a))))]
                       [else
                        (insert-check! l)]))
                   (point-elements (index-result-map fl k))))
               (contours-at-label fl)))]
          [_ #f]))
      n-labels)))

(define prim-applies-to?
  (lambda (prim args)
    (applies-to?
      (Primitive-arity (Name-binder prim))
      (Primitive-arg-types (Name-binder prim))
      (map types-of-point args))))

(define types-of-point
  (lambda (point)
    (list->set (map aval-kind (point-elements point)))))

(define check-summary
  (lambda (unbound)
;    (warn-uncalled)
;    (warn-unused-vars)
    (match-let ([(cons defs n-checks) (pexprs-with-checks tree)])
      (printf "; ~a TOTAL Runtime Checks~%" n-checks)
      (print-abstract-statistics!)
      (cons defs n-checks))))

(define check-output
  (lambda (file unbound)
    (let ([doit (lambda ()
                  (match-let ([(cons defs n-checks) (check-summary unbound)])
                    (for ([def (in-list defs)])
                      (printf "~a~%~%" def))
                    n-checks))])
      (if (string? file)
          (begin
            (with-output-to-file file #:exists 'replace
              (lambda ()
                (printf "#lang racket~%")
                (printf "; Generated by CF Analysis ~a with run-time check optimization ~%"
                        #;cf:version "Racket port"
                        )
                (printf "; (cf:control")
                (for-each (lambda (x) (printf " '~a" x)) (cf:control))
                (printf ")~%")
                (unless (null? unbound)
                  (printf "; CAUTION: ~a are unbound, this code may not be safe~%" unbound))
                (doit)))
            (printf "Optimized program written to file ~a~%" file))
          (doit)))))