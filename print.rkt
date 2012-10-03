#lang racket

(require "library.rkt"
         "abstract.rkt"
         "contour.rkt"
         "callmap.rkt"
         "unparse.rkt"
         "mutrec.rkt")
(provide print-info print-result-map print-val print-call-map print-tree)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Print various information resulting from flow analysis.

(define print-info
  (lambda ()
    (printf "~%Labeled Tree~%")
    (print-tree)
    (printf "~%Result Map,  (Label+Var) x Contour -> 2^Value~%")
    (print-result-map)
    (printf "~%Call Map~%")
    (print-call-map)))

(define print-result-map
  (lambda ()
    (natural-for-each
      (lambda (l)
        (for-each
          (lambda (k)
            (print-val l k (index-result-map l k)))
          (contours-at-label l)))
      n-labels)
    (for-each
      (lambda (x)
        (for-each
          (lambda (k)
            (print-val x k (index-var-map x k)))
          (contours-at-var x)))
      variables)))

(define print-val
  (lambda (x-or-l k v)
    (pretty-print
      `(,@(if (number? x-or-l) `(PT ,x-or-l) `(,(pname* x-or-l)))
        ,(print-contour k)
        =
        ,@(print-point v)))))

(define print-call-map
  (lambda ()
    (natural-for-each
      (lambda (l)
        (let ([call-sites (index-call-map l)]
              [f (pfn (label->node l))])
          (when f
            (if (empty-set? call-sites)
                (printf "~a (~a) is never called~%" f l)
                (printf "~a (~a) is called at ~a~%" f l call-sites)))))
      n-labels)))

(define print-tree
  (lambda ()
    (for-each pretty-print (pexprs-with-labels tree))))
