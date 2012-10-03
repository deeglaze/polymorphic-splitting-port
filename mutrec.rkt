#lang racket
(require (for-syntax racket/syntax syntax/parse))
;; Close the mutually recursive loop with *shudder* mutation.

(define-syntax (mk-global stx)
  (syntax-parse stx
    [(_ x (~optional default
                     #:defaults ([default #'#f])))
     (with-syntax ([set-x! (format-id #'x "set-~a!" #'x)])
             #'(begin (define x default)
                      (define (set-x! v) (set! x v))
                      (provide x set-x!)))]))

;; unparse/flow/init
(mk-global %internal-apply)
(mk-global %not)
(mk-global %cons)
(mk-global %eq?)
(mk-global %<)
(mk-global %eqv?)
(mk-global %equal?)
(mk-global %null?)
(mk-global %pair?)
(mk-global %vector)
(mk-global %make-vector)
(mk-global %vector-ref)
(mk-global %car)
(mk-global %cdr)
(mk-global %read)
(mk-global %eval)
(mk-global %get)
(mk-global %expand-once)
(mk-global %Qvector)
(mk-global %Qlist)
(mk-global %Qcons)
(mk-global %Qbox)
(mk-global %Qmerge-list)
(mk-global %make-closure)
(mk-global %closure-ref)
(mk-global %closure-set!)
(mk-global %box)
(mk-global %unbox)
(mk-global %set-box!)

;; graph-ops/flow/cps/check loop
(mk-global tree)
;; parse/init loop
(mk-global special-env '())
(mk-global basic-env '())
(mk-global quote-env '())
;; parse/unparse loop
(mk-global pcontext)
(mk-global pname*) ;; and flow/print/used-before
;; parse/drivers loop
(mk-global if-warning)
;; flow/abstract loop
(mk-global running-time 0)
(mk-global starting-time 0)
(mk-global variables '()) ;; and print
(mk-global n-labels 0) ;; and check/print/callmap
;; check/unparse loop
(mk-global check-needed?)
;; abstract/contour loop
(mk-global index-var-map)
(mk-global result-map=)
(mk-global index-result-map)
(mk-global p->)
(mk-global p+avals) 
(mk-global split)
(mk-global split-env)
(mk-global aval-kind)
(mk-global aval-label)
(mk-global aenv-lookup)
(mk-global aval-env)
(mk-global point-elements)
(mk-global label->node) ;; and flow/print
;; abstract/check loop
(mk-global contours-at-label)
(mk-global print-abstract-statistics!)
;; check/drivers loop
(mk-global cf:control)

;; init/check loop
(mk-global applies-to?)


