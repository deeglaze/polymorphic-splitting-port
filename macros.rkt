#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Transform functions for essential macros.

(require "data.rkt")
(provide let*-tf cond-tf case-tf delay-tf
         cons-limit quote-tf quasiquote-tf do-tf
         special primitive syntax-err
         set-cons-limit!)

(define special (string->symbol "#special"))
(define primitive (string->symbol "#primitive"))

(define syntax-err
  (lambda (context expr format . args)
    (newline)
    #;(when expr (limited-pretty-print expr 4))
    (apply error #f
      (string-append "Syntax Error~a~a"
        (if (zero? (string-length format))
            ""
            ": ")
        format)
      (if (empty-context? context) "" " ")
      (if (empty-context? context) "" "pcontext unsupported" #;(pcontext context)
          )
      args)))

;(export (cons-limit
;         let*-tf cond-tf case-tf quote-tf quasiquote-tf do-tf)

(define let*-tf
  (lambda (let-expr env context)
    (match let-expr
      [`(,_ () . ,body)
       `(,primitive let () ,@body)]
      [`(,_ ((,(? symbol? s) ,exp)) . ,body)
       `(,primitive let ((,s ,exp)) ,@body)]
      [`(,k ((,(? symbol? s) ,exp) ,rest ...) . ,body)
       `(,primitive let ((,s ,exp)) (,k ,rest ,@body))])))

(define cond-tf
  (lambda (cond-expr env context)
    (let loop ((e (cdr cond-expr)))
      (match e
        [`() `((,primitive void))]
        [`[(else ,b1 . ,body)] `(,primitive begin ,b1 ,@body)]
        [`((else . ,_) . ,_)
         (syntax-err context cond-expr "invalid cond expression")]
        [`((,test => ,proc) . ,rest)
         (let ((g (gensym)))
           `(,primitive let ((,g ,test))
             (,primitive if ,g (,proc ,g) ,(loop rest))))]
        [`((#t ,b1 . ,body)) `(,primitive begin ,b1 ,@body)] ; only diff from Chez?
        [`((,test) . ,rest) `(,primitive or ,test ,(loop rest))]
        [`((,test . ,body) . ,rest)
         `(,primitive if ,test (,primitive begin ,@body) ,(loop rest))]
        [_ (syntax-err context cond-expr "invalid cond expression")]))))

(define case-tf
  (lambda (case-expr env context)
    (let loop ((e (cdr case-expr)))
      (match e
        [`(,exp) `(,primitive begin ,exp ((,primitive void)))]
        [`(,exp (else ,b1 . ,body)) `(,primitive begin ,b1 ,@body)]
        [`(,exp (else . ,_) . ,_)
         (syntax-err context case-expr "invalid case expression")]
        [`(,(? symbol? exp) (,(? list? test) ,b1 . ,body) . ,rest)
         `(,primitive if ((,primitive memv) ,exp (,primitive quote ,test))
           (,primitive begin ,b1 ,@body)
           ,(loop (cons exp rest)))]
        [`(,(? symbol? exp) (,test ,b1 . ,body) . ,rest)
         `(,primitive if ((,primitive memv) ,exp (,primitive quote (,test))) ; Chez extension
           (,primitive begin ,b1 ,@body)
           ,(loop (cons exp rest)))]
        [(cons exp rest)
         (if (not (symbol? exp))
             (let ((g (gensym)))
               `(,primitive let ((,g ,exp))
                 ,(loop (cons g rest))))
             (syntax-err context case-expr "invalid case expression"))]
        [_ (syntax-err context case-expr "invalid case expression")]))))

(define delay-tf
  (lambda (delay-expr env context)
    (match delay-expr
      [(list _ exp)
       `((,primitive make-promise) (,primitive lambda () ,exp))]
      [_ (syntax-err context delay-expr "invalid delay expression")])))

(define cons-limit 8)
(define (set-cons-limit! v) (set! cons-limit v))

(define quote-tf
  (lambda (exp env context)
    (letrec ((qloop
               (match-lambda
                 ((? vector? q) `((,special qvector) ,@(map qloop (vector->list q))))
                 ((? box? q) `((,special qbox) ,(qloop (unbox q))))
                 ((? symbol? q) `(,special quote ,q))
                 ((? null? q) q)
                 ((? list? q)
                  (if (< (length q) cons-limit)
                      `((,special qcons) ,(qloop (car q)) ,(qloop (cdr q)))
                      `((,special qmerge-list) ,@(map qloop q))))
                 ((cons x y) `((,special qcons) ,(qloop x) ,(qloop y)))
                 ((? boolean? q) q)
                 ((? number? q) q)
                 ((? char? q) q)
                 ((? string? q) q)
                 (q (syntax-err context exp "invalid quote expression at ~a" q)))))
      (match exp
        (`(quote ,q) (qloop q))
        ((? vector? q) (qloop q))
        ((? box? q) (qloop q))))))

(define quasiquote-tf
  (lambda (exp env context)
    (letrec ((make-cons
              (lambda (x y)
                (cond ((null? y) `(,(primitive 'list) ,x))
                      ((and (pair? y) (equal? (car y) (primitive 'list)))
                       (cons (car y) (cons x (cdr y))))
                      (else `(,(primitive 'cons) ,x ,y)))))
             (qloop
               (lambda (e n)
                 (match e
                   [`(quasiquote ,e)
                    (make-cons 'quasiquote (qloop `(,e) (+ 1 n)))]
                   [(list 'unquote e)
                    (if (zero? n)
                        e
                        (make-cons 'unquote (qloop `(,e) (- n 1))))]
                   [`(unquote-splicing ,e)
                    (if (zero? n)
                        e
                        (make-cons 'unquote-splicing (qloop `(,e) (- n 1))))]
                   [(cons (list 'unquote-splicing e) y)
                    (=> fail)
                    (if (zero? n)
                        (if (null? y)
                            e
                            `(,(primitive 'append) ,e ,(qloop y n)))
                        (fail))]
                   [(? box? q) `(,(primitive 'box) ,(qloop (unbox q) n))]
                   [(? symbol? q)
                    (if (memq q '(quasiquote unquote unquote-splicing))
                        (syntax-err context exp
                          "invalid use of ~a inside quasiquote" q)
                        `(quote ,q))]
                   [(? null? q) q]
                   [(cons x y) (make-cons (qloop x n) (qloop y n))]
                   [(? vector? q) `(,(primitive 'vector)
                                    ,@(map (lambda (z) (qloop z n))
                                           (vector->list q)))]
                   [(? boolean? q) q]
                   [(? number? q) q]
                   [(? char? q) q]
                   [(? string? q) q]
                   [q (syntax-err context exp
                        "invalid quasiquote expression at ~a" q)]))))
      (match exp
        (`(quasiquote ,q) (qloop q 0))))))

(define do-tf
  (lambda (do-expr env context)
    (let loop ((e (cdr do-expr)))
      (match e
;        (((var init . step) ...) (e0 e1 ...) c ...)
        [(list-rest (? list? vis) (cons e0 (? list? e1)) (? list? c))
         (if (andmap (match-lambda
                       [(list-rest _ _ _) #t]
                       [_ #f])
               vis)
             (let* ((var (map car vis))
                    (init (map cadr vis))
                    (step (map cddr vis))
                    (step (map (lambda (v s)
                                 (match s
                                   [`() v]
                                   [`(,e) e]
                                   [_ (syntax-err context do-expr
                                        "invalid do expression")]))
                               var
                               step)))
               (let ((doloop (gensym)))
                 (match e1
                   ['()
                    `(let ,doloop ,(map list var init)
                       (if (not ,e0)
                           (begin ,@c (,doloop ,@step) (void))
                           (void)))]
                   [(list body0 body ...)
                    `(let ,doloop ,(map list var init)
                       (if ,e0
                           (begin ,body0 ,@body)
                           (begin ,@c (,doloop ,@step))))]
                   [_ (syntax-err context do-expr "invalid do expression")])))
             (syntax-err context do-expr "invalid do expression"))]
        (_ (syntax-err context do-expr "invalid do expression"))))))

;)
