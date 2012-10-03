#lang racket

(require "env.rkt"
         "mutrec.rkt")

(define (set-prims! initial-env special-env)
  (set-%not! (lookup initial-env 'not))
  (set-%cons! (lookup initial-env 'cons))
  (set-%eq?! (lookup initial-env 'eq?))
  (set-%<! (lookup initial-env '<))
  (set-%eqv?! (lookup initial-env 'eqv?))
  (set-%equal?! (lookup initial-env 'equal?))
  (set-%null?! (lookup initial-env 'null?))
  (set-%pair?! (lookup initial-env 'pair?))
  (set-%vector! (lookup initial-env 'vector))
  (set-%make-vector! (lookup initial-env 'make-vector))
  (set-%vector-ref! (lookup initial-env 'vector-ref))
  (set-%car! (lookup initial-env 'car))
  (set-%cdr! (lookup initial-env 'cdr))
  (set-%read! (lookup initial-env 'read))
  (set-%eval! (lookup initial-env 'eval))
  (set-%get! (lookup initial-env 'eval))
  (set-%expand-once! (lookup initial-env 'eval))

  (set-%internal-apply! (lookup special-env 'internal-apply))
  (set-%Qvector! (lookup special-env 'qvector))
  (set-%Qlist! (lookup special-env 'qlist))
  (set-%Qcons! (lookup special-env 'qcons))
  (set-%Qbox! (lookup special-env 'qbox))
  (set-%Qmerge-list! (lookup special-env 'qmerge-list))

  (set-%make-closure! (lookup special-env 'make-closure))
  (set-%closure-ref! (lookup special-env 'closure-ref))
  (set-%closure-set!! (lookup special-env 'closure-set!))

  (set-%box! (lookup initial-env 'box))
  (set-%unbox! (lookup initial-env 'unbox))
  (set-%set-box!! (lookup initial-env 'set-box!)))