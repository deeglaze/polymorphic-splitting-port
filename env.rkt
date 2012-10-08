#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environments
;;
;; A simple implementation of environments as association lists.

(provide empty-env empty-env?
         lookup lookup? bound? extend-env extend-env*
         join-env env->list env-domain env-range
         env-restrict
         env-map
         filter-env)

(define empty-env '())

(define empty-env? null?)

(define lookup
  (lambda (env x)
    (match (assq x env)
      [#f (error 'lookup "no binding for ~s (~a)" x env)]
      [(cons _ b) b])))

(define lookup?
  (lambda (env x)
    (match (assq x env)
      [#f #f]
      [(cons _ b) b])))

(define bound?
  (lambda (env x)
    (match (assq x env)
      [#f #f]
      [_ #t])))

(define extend-env
  (lambda (env x v)
    (cons (cons x v) env)))

(define extend-env*
  (lambda (env xs vs)
    (append (map cons xs vs) env)))

(define join-env
  (lambda (env newenv)
    (append newenv env)))

(define env->list
  (lambda (env)
    (let loop ([env env] [seen '()])
      (cond [(null? env) env]
            [(memq (caar env) seen) (loop (cdr env) seen)]
            [else (let ([d (loop (cdr env) (cons (caar env) seen))])
                    (if (eq? d (cdr env))
                        env
                        (cons (car env) d)))]))))

(define env-domain
  (lambda (env)
    (map car (env->list env))))

(define env-range
  (lambda (env)
    (map cdr (env->list env))))

(define env-restrict
  (lambda (env domain)
    (filter
      (match-lambda [(cons x v) (memq x domain)])
      (env->list env))))

(define env-map
  (lambda (f env)
    (map (match-lambda ((cons x v) (cons x (f x v))))
         (env->list env))))

(define filter-env
  (lambda (f env)
    (let loop ([env (env->list env)])
      (cond [(null? env) env]
            [(f (caar env)) (cons (car env) (loop (cdr env)))]
            [else (loop (cdr env))]))))
