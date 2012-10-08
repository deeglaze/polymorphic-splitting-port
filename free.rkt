 #lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Find free variables of an expression or program.
;;
;; Primitives are not counted as free.
;; Lambda's cache their free set to speed lookup.

(require "ordset-list.rkt"
         "data.rkt"
         racket/trace
         (for-syntax syntax/parse))
(provide free-in-defs free-in-exp free-names)

; have to move this out here cause export does not work correctly
(define NameSet (ordset
                  (lambda (x y) (< (Name-id x) (Name-id y)))
                  (lambda (x y) (= (Name-id x) (Name-id y)))))

(define nameset (order-set NameSet))
(define nameset-union (order-union NameSet))
(define nameset-difference (order-difference NameSet))
(define nameset->list (order-set->list NameSet))
(define list->nameset (order-list->set NameSet))

(define-syntax (for/nameset-union stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:initial init:expr)
                   #:defaults ([init #'(nameset)]))
        guards body1 body ...)
     #`(for/fold/derived #,stx ([res init]) guards
         (nameset-union res (let () body1 body ...)))]))

(define free
  (lambda (e)
    (match e
      [(Define _ exp) (free exp)]
      [(E: (Var x)) (nameset x)]
      [(E: (Lam: names body))
       (or (Lam-free (E-exp e))
           (let ([fv (nameset-difference (free body)
                                         (list->nameset names))])
             (set-Lam-free! (E-exp e) fv)
             fv))]
      [(E: (Vlam: names rest body))
       (or (Vlam-free (E-exp e))
           (let ([fv (nameset-difference (free body) (list->nameset (cons rest names)))])
             (set-Vlam-free! (E-exp e) fv)
             fv))]
      [(E: (App e0 args))
       (for/nameset-union #:initial (free e0)
           ([arg (in-list args)])
         (free arg))]
      [(E: (Let b e2))
       (for/nameset-union
        #:initial (nameset-difference (free e2)
                                      (list->nameset (definition-names b)))
           ([cl (in-list b)])
         (free cl))]
      [(E: (Letr b e2))
       (nameset-difference
        (for/nameset-union #:initial (free e2)
           ([cl (in-list b)])
         (free cl))
        (list->nameset (definition-names b)))]
      [(E: (or (And exps) (Or exps) (Begin exps)))
       (for/nameset-union ([exp (in-list exps)])
         (free exp))]
      [(E: (If test then els))
       (nameset-union
        (free test)
        (nameset-union
         (free then)
         (free els)))]
      [(E: (Set! x body))
       (nameset-union (nameset x) (free body))]
      [(E: (Letcc x e1))
       (nameset-difference
        (free e1)
        (nameset x))]
      [_ (nameset)])))

(define (free-in-exp e)
  (define names (free e))
  (define namelist (nameset->list names))
  (filter-not Name-primitive? namelist))

(define free-in-defs
  (lambda (defs-and-exps)
    (nameset->list
     (nameset-difference
      (for/nameset-union ([exp (in-list defs-and-exps)]) (free-in-exp exp))
      (list->nameset
       (for/list ([e (in-list defs-and-exps)] #:when (Define? e))
         (Define-name e)))))))

(define free-names
  (lambda (e)
    (nameset->list (free e))))
