#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial environments, etc.

(require "env.rkt"
         "data.rkt"
         "parse.rkt"
         "mutrec.rkt")
(provide initial-env meets-arity?
         init-envs!)

;; This file exports:
;;  initial-env - initial R4RS environment
;;  meets-arity? - for testing arity match

(define initial-info
  ;  name           type        optional-attribute(s)
  ; where optional-attribute(s) are any of:
  ;  (S tag con-index)            is a selector
  ;  (P tag ...)                  is a predicate
  ;  (C tag)                      is a constructor
  ;  (M tag con-index val-index)  is a mutator
  ;  (X)                          applications with constant args may be simplified
  ;  (A)                          allocates
  ;  (R)                          uses global state
  ;  (W)                          modifies global state, diverges, or raises an error
  ;                                   when applied type correct
  '(; booleans
    (not            (_ -> (+ true false))                             (X))

    ; equivalence predicates
    (eqv?           (_ _ -> (+ true false))                           (R) (X))
    (eq?            (_ _ -> (+ true false))                           (R) (X))
    (equal?         (_ _ -> (+ true false))                           (W))

    ; pairs and lists
    (cons           (_ _ -> cons)                                     (C cons) (A))
    (car            (cons -> _)                                       (S cons 0) (R))
    (cdr            (cons -> _)                                       (S cons 1) (R))
    (set-car!       (cons _ -> void)                                  (M cons 0 1) (W))
    (set-cdr!       (cons _ -> void)                                  (M cons 1 1) (W))
 
    ; symbols
    (symbol->string (sym -> str)                                      (X))
    (string->symbol (str -> sym)                                      (X))

    ; numbers
    (complex?       (_ -> (+ true false))                             (X))
    (real?          (_ -> (+ true false))                             (X))
    (rational?      (_ -> (+ true false))                             (X))
    (integer?       (_ -> (+ true false))                             (X))
    (exact?         (num -> (+ true false))                           (X))
    (inexact?       (num -> (+ true false))                           (X))
    (=              (num num (&list num) -> (+ true false))           (X))
    (<              (num num (&list num) -> (+ true false))           (X))
    (>              (num num (&list num) -> (+ true false))           (X))
    (<=             (num num (&list num) -> (+ true false))           (X))
    (>=             (num num (&list num) -> (+ true false))           (X))
    (zero?          (num -> (+ true false))                           (X))
    (positive?      (num -> (+ true false))                           (X))
    (negative?      (num -> (+ true false))                           (X))
    (odd?           (num -> (+ true false))                           (X))
    (even?          (num -> (+ true false))                           (X))
    (max            (num (&list num) -> num)                          (X))
    (min            (num (&list num) -> num)                          (X))
    (+              ((&list num) -> num)                              (X))
    (*              ((&list num) -> num)                              (X))
    (-              (num (&list num) -> num)                          (X))
    (/              (num (&list num) -> num)                          (W))
    (abs            (num -> num)                                      (X))
    (quotient       (num num -> num)                                  (W))
    (remainder      (num num -> num)                                  (W))
    (modulo         (num num -> num)                                  (W))
    (gcd            ((&list num) -> num)                              (X))
    (lcm            ((&list num) -> num)                              (X))
    (numerator      (num -> num)                                      (X))
    (denominator    (num -> num)                                      (X))
    (floor          (num -> num)                                      (X))
    (ceiling        (num -> num)                                      (X))
    (truncate       (num -> num)                                      (X))
    (round          (num -> num)                                      (X))
    (rationalize    (num num -> num)                                  (X))
    (exp            (num -> num)                                      (X))
    (log            (num -> num)                                      (W))
    (sin            (num -> num)                                      (X))
    (cos            (num -> num)                                      (X))
    (tan            (num -> num)                                      (X))
    (asin           (num -> num)                                      (X))
    (acos           (num -> num)                                      (X))
    (atan           (num (&optional num) -> num)                      (X))
    (sqrt           (num -> num)                                      (X))
    (expt           (num num -> num)                                  (X))
    (make-rectangular (num num -> num)                                (X))
    (make-polar     (num num -> num)                                  (X))
    (real-part      (num -> num)                                      (X))
    (imag-part      (num -> num)                                      (X))
    (magnitude      (num -> num)                                      (X))
    (angle          (num -> num)                                      (X))
    (exact->inexact (num -> num)                                      (X))
    (inexact->exact (num -> num)                                      (X))
    (number->string (num (&optional num) -> str)                      (X))
    (string->number (str (&optional num) -> num)                      (X))

    ; characters
    (char=?         (char char -> (+ true false))                     (X))
    (char<?         (char char -> (+ true false))                     (X))
    (char>?         (char char -> (+ true false))                     (X))
    (char<=?        (char char -> (+ true false))                     (X))
    (char>=?        (char char -> (+ true false))                     (X))
    (char-ci=?      (char char -> (+ true false))                     (X))
    (char-ci<?      (char char -> (+ true false))                     (X))
    (char-ci>?      (char char -> (+ true false))                     (X))
    (char-ci<=?     (char char -> (+ true false))                     (X))
    (char-ci>=?     (char char -> (+ true false))                     (X))
    (char-alphabetic? (char -> (+ true false))                        (X))
    (char-numeric?  (char -> (+ true false))                          (X))
    (char-whitespace? (char -> (+ true false))                        (X))
    (char-upper-case? (char -> (+ true false))                        (X))
    (char-lower-case? (char -> (+ true false))                        (X))
    (char->integer  (char -> num)                                     (X))
    (integer->char  (num -> char)                                     (W))
    (char-upcase    (char -> char)                                    (X))
    (char-downcase  (char -> char)                                    (X))

    ; strings
    (make-string    (num (&optional char) -> str)                     (A))
    (string         ((&list char) -> str)                             (A))
    (string-length  (str -> num)                                      (X) (R))
    (string-ref     (str num -> char)                                 (R))
    (string-set!    (str num char -> void)                            (W))
    (string=?       (str str -> (+ true false))                       (X))
    (string<?       (str str -> (+ true false))                       (X))
    (string>?       (str str -> (+ true false))                       (X))
    (string<=?      (str str -> (+ true false))                       (X))
    (string>=?      (str str -> (+ true false))                       (X))
    (string-ci=?    (str str -> (+ true false))                       (X))
    (string-ci<?    (str str -> (+ true false))                       (X))
    (string-ci>?    (str str -> (+ true false))                       (X))
    (string-ci<=?   (str str -> (+ true false))                       (X))
    (string-ci>=?   (str str -> (+ true false))                       (X))
    (substring      (str num num -> str)                              (W))
    (string-append  ((&list str) -> str)                              (R))
    (string-copy    (str -> str)                                      (R))
    (string-fill!   (str char -> void)                                (W))

    ; vectors
    (make-vector    (num (&optional _) -> vec)                        (C vec) (A))
    (vector         ((&list _) -> vec)                                (C vec) (A))
    (vector-length  ((+ vec0 vec) -> num)                             (X) (R))
    (vector-ref     ((+ vec0 vec) num -> _)                           (S vec 0) (R))
    (vector-set!    ((+ vec0 vec) num _ -> void)                      (M vec 0 2) (W))
    (vector-fill!   ((+ vec0 vec) _ -> void)                          (M vec 0 1) (W))

    ; input and output
    (input-port?           (_ -> (+ true false))                      (P (iport)))
    (output-port?          (_ -> (+ true false))                      (P (oport)))
    (current-input-port    (-> iport)                                 (R))
    (current-output-port   (-> oport)                                 (R))
    (open-input-file       (str -> iport)                             (R))
    (open-output-file      (str -> oport)                             (R))
    (close-input-port      (iport -> void)                            (W))
    (close-output-port     (oport -> void)                            (W))
    (read                  ((&optional iport) -> (+))                 (W))  ; handled specially in flow.scm
    (read-char             ((&optional iport) -> (+ char eof))        (W))
    (peek-char             ((&optional iport) -> (+ char eof))        (R))
    (char-ready?           ((&optional iport) -> (+ true false))      (R))
    (write                 (_ (&optional oport) -> void)              (W))
    (display               (_ (&optional oport) -> void)              (W))
    (newline               ((&optional oport) -> void)                (W))
    (write-char            (char (&optional oport) -> void)           (W))

    ; system interface
    (load           (str -> void)                                     (W))
    (transcript-on  (str -> void)                                     (W))
    (transcript-off (-> void)                                         (W))

    ; non R4RS extensions

    ; misc
    (symbol-append  ((&list _) -> sym)                                (X))
    (box            (_ -> box)                                        (C box) (A))
    (unbox          (box -> _)                                        (S box 0) (R))
    (set-box!       (box _ -> void)                                   (M box 0 1) (W))
    (void           (-> void)                                         (X))
    (raise          ((&list _) -> (+))                                (W))

    ; Chez extensions
    (error          ((&list _) -> (+))                                (W))
    (reset          (-> (+))                                          (W))
    (gensym         (-> sym)                                          (W))
    (pretty-print   (_ (&optional oport) -> void)                     (W))
    (printf         (str (&list _) -> void)                           (W))
    (format         (str (&list _) -> void)                           (W))
    (cpu-time       (-> num)                                          (W))
    (real-time      (-> num)                                          (W))
    (collect        ((&optional num) -> void)                         (W))
    (flush-output   ((&optional oport) -> void)                       (W))
    (compile-file   (str str -> void)                                 (W))
    (print-length   ((&optional (+ num false)) -> (+ num false))      (W))
    (pretty-maximum-lines ((&optional (+ num false)) -> (+ num false)) (W))
    (print-level    ((&optional (+ num false)) -> (+ num false))      (W))
    (gensym-prefix  ((&optional str) -> str)                          (W))
    (gensym-count   ((&optional num) -> num)                          (W))
    (fl+            ((&list num) -> num)                              (W))
    (fl*            ((&list num) -> num)                              (W))
    (fl-            (num (&list num) -> num)                          (W))
    (fl/            (num (&list num) -> num)                          (W))
    (fx+            ((&list num) -> num)                              (W))
    (fx*            ((&list num) -> num)                              (W))
    (fx-            (num (&list num) -> num)                          (W))
    (fx/            (num (&list num) -> num)                          (W))
    (fx=            (num num (&list num) -> (+ true false))           (W))
    (fx<            (num num (&list num) -> (+ true false))           (W))
    (fx>            (num num (&list num) -> (+ true false))           (W))
    (fx<=           (num num (&list num) -> (+ true false))           (W))
    (fx>=           (num num (&list num) -> (+ true false))           (W))
    (fxlogand       ((&list num) -> num)                              (W))
    (fxlogor        ((&list num) -> num)                              (W))
    (fxlognot       (num -> num)                                      (W))
    (delete-file    (str -> void)                                     (W))
    (file-exists?   (str -> (+ true false))                           (R))
    (current-directory ((&optional str) -> void)                      (W))
    (eval           (_ -> (+))                                        (W))  ; handled specially in flow.scm
    (get            (_ -> (+))                                        (W))  ; handled specially in flow.scm
    (expand-once    (_ -> (+))                                        (W))  ; handled specially in flow.scm
    (optimize-level ((&optional num) -> (+ void num))                 (W))

    ; for match
    (match:error    (_ (&list _) -> (+))                              (W))

    ; predicates
    (number?        (_ -> (+ true false))                             (X) (P (num)))
    (null?          (_ -> (+ true false))                             (X) (P (nil)))
    (char?          (_ -> (+ true false))                             (X) (P (char)))
    (symbol?        (_ -> (+ true false))                             (X) (P (sym)))
    (string?        (_ -> (+ true false))                             (X) (P (str)))
    (vector?        (_ -> (+ true false))                             (X) (P (vec)))
    (box?           (_ -> (+ true false))                             (X) (P (box)))
    (pair?          (_ -> (+ true false))                             (X) (P (cons)))
    (procedure?     (_ -> (+ true false))                             (X) (P (closure cont)))
    (eof-object?    (_ -> (+ true false))                             (X) (P (eof)))
    (input-port?    (_ -> (+ true false))                             (X) (P (iport)))
    (output-port?   (_ -> (+ true false))                             (X) (P (oport)))
    (boolean?       (_ -> (+ true false))                             (X))
    (list?          (_ -> (+ true false))                             (X))
  ))

(define special-info
  '((qcons          (_ _ -> cons)                                     (C cons) (A))
    (qbox           (_ -> box)                                        (C box) (A))
    (qvector        ((&list _) -> vec)                                (C vec) (A))
    (qlist          ((&list _) -> (+))                                (A))
    (qmerge-list    ((&list _) -> (+))                                (A))
    ; handles
    (make-handle    (_ -> handle)                                     (R))
    (handle-ref     (handle _ -> _)                                   (S handle 0) (R))
    (handle-set!    (handle _ -> void)                                (M handle 0 1) (W))

    (make-closure   (_ (&list _) -> (+))                              (A))
    (closure-ref    (_ _ -> (+))                                      (R))
    (closure-set!   (_ _ _ -> void)                                   (W))
    (closure?       (_ -> (+ true false))                             )
    (internal-apply (_ (&list _) -> (+))                              (W))
    ))

(define init-prim
  (lambda (make-print-name)
    (lambda (l env)
      (match l
        [(list-rest name type attr)
         (let ([find-attr (lambda (x)
                            (let ((r (assq x attr)))
                              (and r (cdr r))))])
           (extend-env env name
             (let ([n (make-Name (make-print-name name) '())])
               (set-Name-binder! n
                 (let-values ([(arity args result) (parse-type type)])
                   (Primitive
                     (cond
                       ((find-attr 'C)
                        => (lambda (x) (Constructor (car x))))
                       ((find-attr 'P)
                        => (lambda (x) (Predicate (car x))))
                       ((find-attr 'S)
                        => (lambda (x) (Selector (car x) (cadr x))))
                       ((find-attr 'M)
                        => (lambda (x) (Mutator (car x) (cadr x) (caddr x))))
                       (else (Simple)))
                     arity
                     args
                     result
                     (if (find-attr 'X) #t #f)
                     (cond [(find-attr 'W) 'W]
                           [(find-attr 'R) 'R]
                           [(find-attr 'A) 'A]
                           [else #f]))))
               n)))]))))


;; Parse a type description into
;;  arity description, which is one of:
;;      positive integer N     - fixed arity
;;      (N N+1) for N positive - N args plus 1 optional
;;      negative N             - -N or more
;;  argument constructor list list
;;  result constructor list

(define parse-type
  (letrec ([parse-union
             (match-lambda
               ['_ '_]
               [(? symbol? s) (list s)]
               [(cons '+ results) results])])
    (lambda (t)
      (let loop ([t t] [arity 0] [args '()] [opt #f] [var #f])
        (match (car t)
          ['->
            (let ([arity-list (cond (opt (list arity (+ 1 arity)))
                                    (var (list (- (- arity) 1)))
                                    (else (list arity)))]
                  (result (parse-union (cadr t))))
              (values arity-list (reverse args) result))]
          [`(&list ,a)
           (loop (cdr t) arity (cons (parse-union a) args) opt #t)]
          [`(&optional ,a)
           (loop (cdr t) arity (cons (parse-union a) args) #t var)]
          [a
           (loop (cdr t) (+ 1 arity) (cons (parse-union a) args) opt var)])))))

(define meets-arity?
  (lambda (arity-spec nargs)
    (ormap
      (lambda (n)
        (or (= n nargs)
            (and (negative? n) (<= (- (- n) 1) nargs))))
      arity-spec)))

(set-applies-to?!
  (lambda (arity-spec type-spec arg-types)
    (and (meets-arity? arity-spec (length arg-types))
         (let loop ([provided arg-types] [required type-spec])
           (or (null? provided)
               (and (andmap
                      (lambda (t)
                        (or (eq? '_ (car required)) (memq t (car required))))
                      (car provided))
                    (loop (cdr provided)
                          (if (null? (cdr required))
                              required
                              (cdr required)))))))))

(define initial-env #f)

(define (init-envs!)
  (set! initial-env
        (foldr (init-prim (lambda (x) x))
               basic-env
               initial-info))
  (set-special-env!
   (foldr (init-prim (lambda (x) x))
          quote-env
          special-info)))
