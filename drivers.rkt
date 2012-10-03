#lang racket

(require "library.rkt"
         "data.rkt"
         "mutrec.rkt"
         "parse.rkt"
         "unparse.rkt"
         "r4rsprim.rkt"
         "contour.rkt"
         "check.rkt"
         "flags.rkt"
         "macros.rkt"
         "flow.rkt"
         "free.rkt"
         "init.rkt"
         "print.rkt"
         "cps.rkt")

(provide cf:help
         cf:base
         cf:check
         cf:value
         cf:tree
         cf:run
         cf:map
         cf:cps
         cf:
         init!)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Drivers


(define verbose #f)
(define times #f)
(define *max-inline-cost* 20)
(define *unreasonable-cost* (+ *max-inline-cost* 1))
(define *thresholdList* '(10 20 30 50 100 500))
(define *inline?* #f)
(define suffix-string "")
(define Contour 'poly)
(define *staticCounts* #t)
(define *dynamicCounts* #f)

(define process-def                 ; analyse and optimize a definition
  (lambda (exp optimization output)
    (parameterize ([pretty-print-depth #f]
                   #;[print-length #f]
                   #;[pretty-maximum-lines #f]
                   #;[gensym-prefix "G"]
                   #;[gensym-count 1]
                   )
      (let* ([before-parse (current-inexact-milliseconds)]
	     [unbound (begin
			(parse exp)
                        (printf "Finished parse.~%")
			(when cps? (cps-tree)))]
	     [before-analysis (current-inexact-milliseconds)]
	     [print-warnings (analyse)]
	     [before-opt (current-inexact-milliseconds)]
             [_ (begin (optimization))]
             [before-output (current-inexact-milliseconds)]
             [result (output unbound)]
             [before-end (current-inexact-milliseconds)])
        (when times
          (printf "~a seconds parsing,~%"
            (exact->inexact (/ (- before-analysis before-parse) 1000)))
          (printf "~a seconds analysing,~%"
            (exact->inexact (/ (- before-opt before-analysis) 1000)))
          (printf "~a seconds optimizing,~%"
            (exact->inexact (/ (- before-output before-opt) 1000)))
          (printf "~a seconds writing output.~%"
            (exact->inexact (/ (- before-end before-output) 1000))))
        result))))

(define parse
  (lambda (sexp)
    (match (parse-def `(begin ,@r4rs-prims) initial-env initial-env)
      [(list prefix env unbound-prefix)
       (when (pair? unbound-prefix)
         (printf "Unbound prefixes! ~a~%" unbound-prefix))
       (match (parse-def sexp env env)
         [(list defs _ unbound)
          (define prefix* (filter (let ([free (free-in-defs defs)])
			    (lambda (d) (memq (Define-name d) free)))
			  prefix))
          (unless (null? prefix*)
            (printf "Note: prefixing ~a~%" (map (lambda (d) (pname* (Define-name d))) prefix*)))
          (let* ([defs (append prefix* defs)])
            (set-tree! (make-E (Letr defs (make-E (Const (void))))))
            unbound)]
         [err (error 'parse "Bad sexp ~a" err)])]
      [err (error 'parse "Bad prefix ~a" err)])))

(define init!
  (lambda ()
    (set-tree! '())
    (set-cps?! #f)
    (set-if-warning! #t)
    (cf:help)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interface routines for analysis control and inspection

(set-cf:control!
  (lambda args
    (let ((dbg (match-lambda
                 ('verbose (set! verbose #t))
                 ('!verbose (set! verbose #f))
                 ('times (set! times #t))
                 ('!times (set! times #f))
                 ('if-split (set-If-split! #t))
                 ('!if-split (set-If-split! #f))
                 ('const-split (set-Const-split! #t))
                 (`(const-split ,(? symbol? syms) ...) (set-Const-split! syms))
                 ('!const-split (set-Const-split! #f))
                 ('if-warning (set-if-warning! #t))
                 ('!if-warning (set-if-warning! #f))
                 (`(cons-limit ,(? number? n)) (set-cons-limit! n))
                 (`(inline-cost ,(? number? n))
		  (set! *max-inline-cost* n)
		  (set! *unreasonable-cost* (+ n 1)))
                 ('stats (set! *dynamicCounts* #t))
                 ('!stats (set! *dynamicCounts* #f))
                 (x (begin
                      (install-contour! x)
                      (set! Contour x))))))
      (if (null? args)
          (list
            Contour
            (if If-split 'if-split '!if-split)
            (if Const-split 'const-split '!const-split)
            (if verbose 'verbose '!verbose)
            (if times 'times '!times)
            `(cons-limit ,cons-limit)
	    `(inline-cost ,*max-inline-cost*)
	    (if (or *staticCounts* *dynamicCounts*) 'stats '!stats))
          (for-each dbg args)))))

;(define cf:defprim
;  (match-lambda*
;    (((? symbol? x) type)
;     (defprim x type 'impure))
;    (((? symbol? x) type (? symbol? mode))
;     (defprim x type mode))
;    (args (use-error "Invalid command ~a" `(cf:defprim ,@args)))))


(define cf:help
  (lambda ()
    (printf "Commands for CF Scheme (~a)~%" #;cf:version "Racket port"
            )
    (printf "  (cf:         file (output))    analyse a file and execute~%")
    (printf "  (cf:check    file (output))    insert run-time checks~%")
    (printf "  (cf:value    label)            print values at label~%")
    (printf "  (cf:tree)                      print labeled tree~%")
    (printf "  (cf:run      file)             run analysed file~%")
    (printf "  (cf:run3     file)             run analysed file at opt 3~%")
    (printf "  (cf:run2     file)             run analysed file at opt 2~%")
    (printf "  (cf:run*     file)             run analysed file at opt 3 unsafe~%")
    (printf "  (cf:map     [file])            print result map~%")
    (printf "  (cf:help)                      prints this message~%")
    (printf "  (cf:control  flag ...)         set internal flags~%")
    (printf "  (cf:cps     file (output))     analyse cps'ed file~%")
    ;; Ian: undefined
    ;;(printf "  (cf:cps-type     file (output))     analyse cps'ed file using type analysis~%")
    ;;(printf "  (cf:cps-poly     file (output))     analyse cps'ed file using old analysis~%")
    ))

(define cf:map
  (lambda args
    (cond ((null? args)
           (print-info))
          ((and (= 1 (length args)) (string? (car args)))
           (with-output-to-file (car args) print-info #:exists 'replace))
          (else (error "Bad args to cf:map")))))

(define cf:value
 display)

(define cf:tree
  (lambda ()
    (print-tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cf:
  (lambda args
    (init-parse!)
    (init-envs!) ;; depends on init-parse
    (match-let ([(cons input output-file) (apply parse-in-out args)])
      (printf "Finished load.~%")
      (process-def
        input
        insert-runtime-checks
        (lambda (unbound)
          (match output-file
            [(or #f #t) (error "Output file required to run")]
            [_ (check-summary unbound)
               (check-output output-file unbound)
               (printf "Executing ...~%")
               (flush-output)
               (cf:run output-file)])
          (void))))))

(define cf:run
  (lambda (file)
    (unless (eq? 'slow loaded-checks)
        (printf "Loading slow CHECKs...~%")
        (load "checklib.scm")
        (set! loaded-checks 'slow))
    (load file)
    #;
    (parameterize ([read-accept-reader #t])
      (define expr (compile (with-input-from-file file read-syntax)))
      (printf "Compiled.~%")
      (eval expr (make-base-namespace)))))

(define (start-run file)
  ;;(init-counters!) ;; Ian: undefined O_o
  (let ((object (string-append file ".so"))
	(*avgCount* (if *dynamicCounts* 1.0 3.0)))
    ;;(compile-file file object)
    (let loop ((i 1)
	       (curTime 0.0)
               #;(gcTime 0.0)
               )
      (collect-garbage)
      (cond ((> i *avgCount*)
	     (list curTime
		   ;;gcTime
		   ;;(- curTime gcTime)
                   ;; Ian: undefined
		   ;;*primCount*
		   ;;*refCount*
		   ;;*appCount*
		   ;;*lamCount*
                   ))
	    (else (let* ((start (current-inexact-milliseconds))
                         ;;(start-gc-time (sstats-gc-cpu (statistics)))
			 (_ (load object))
			 (end (current-inexact-milliseconds))
                         #;(end-gc-time (sstats-gc-cpu (statistics)))
			 (thisTime (exact->inexact
					   (* (- end start) clock-granularity)))
			 #;
                         (thisGcTime (exact->inexact
                                      (* (- end-gc-time start-gc-time)
                                         clock-granularity))))
		    (loop (+ i 1)
			  (if (= i 1)
			      thisTime
			      (if (< thisTime curTime) thisTime curTime))
			  #;
                          (if (= i 1)
			      thisGcTime
			      (if (< thisTime curTime) thisGcTime gcTime)))))))))


;; Return a pair of input s-expr and output name
(define parse-in-out
  (let ([file->def (lambda (f) `(begin ,@(readfile f)))])
    (case-lambda
        [(x y) (match* (x y)
                 [((? string? input)
                   (and output (or (? string?) #f)))
                  (cons (file->def input) output)]
                 [((list (? string? input) ...)
                   (and output (or (? string?) #f)))
                  (cons `(begin ,@(map file->def input)) output)]
                 [(input
                   (and output (or (? string?) #f)))
                  (cons input output)])]
      [(x) (match x
             [(? string? input)
              (cons (file->def input) (string-append (strip-suffix input) suffix-string))]
             [(list (? string? input) ...)
              (error "Output file name required")]
             [input (cons input #t)])])))

(define strip-suffix
  (lambda (name)
    (let ((n (string-length name)))
      (or (and (<= 3 n) (equal? ".ss" (substring name (- n 3) n))
               (substring name 0 (- n 3)))
          (and (<= 4 n) (member (substring name (- n 4) n) '(".scm" ".cps"))
               (substring name 0 (- n 4)))))))

(define ifile->ofile
  (lambda (ifile suffix)
    (string-append (or (strip-suffix ifile) ifile) suffix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inline-output
  (lambda (file unbound tree)
    (let ([doit (lambda ()
                  (for-each pretty-write (pexprs-with-checks tree)))])
      (if (string? file)
          (begin
            (with-output-to-file file
              (lambda () (printf "#lang racket~%")
                      (doit))
              #:exists 'replace)
	    (printf "Optimized program written to file ~a~%" file))
	  (begin (doit))))))

(define cf:cps
  (lambda args
    (set! suffix-string ".cps")
    (init-cps!)
    (init-parse!)
    (init-envs!) ;; depends on init-parse
    (install-contour! 'poly)
    (match-let ([(cons input output-file) (apply parse-in-out args)])
      (process-def
        input
	insert-runtime-checks
        (lambda (unbound)
          (match output-file
            [#f (check-summary unbound)]
            [#t (check-output output-file unbound)]
	    [_ (check-summary unbound)
               (check-output output-file unbound)])
          (void))))))

(define loaded-checks 'slow)

#;(set-cf:run3*!
 (lambda (file)
   (parameterize ((optimize-level 3))
     (unless (eq? 'fast loaded-checks)
       (unless fastlibrary-file
         (use-error "No loaded-checks mode in this version"))
       (printf "Loading fast CHECKs...~%")
       (load (string-append installation-directory fastlibrary-file))
       (set! loaded-checks 'fast))
     (load file))))


(define cf:base
  (lambda args
    (set! suffix-string ".cf")
    (set-cps?! #f)
    (init-parse!)
    (init-envs!) ;; depends on init-parse
    (install-contour! 'poly)
    (match-let ([(cons input output-file) (apply parse-in-out args)])
      (process-def
        input
        insert-runtime-checks
        (lambda (unbound)
          (match output-file
            [#f (check-summary unbound)]
            [#t (check-output output-file unbound)]
            [_ (check-summary unbound)
               (check-output output-file unbound)])
          (void))))))

(define cf:check
  (lambda args
    (init-parse!)
    (init-envs!) ;; depends on init-parse
    (match-let ([(cons input output-file) (apply parse-in-out args)])
      (process-def
        input
        insert-runtime-checks
        (lambda (unbound)
          (match output-file
            [#f (check-summary unbound)]
            [#t (check-output output-file unbound)]
            [_ (check-summary unbound)
               (check-output output-file unbound)])
          (void))))))

(cf: "/home/ianj/projects/polymorphic-splitting/boyer.scm")