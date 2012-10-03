#lang racket

(require "ordset-list.rkt"
         "library.rkt"
         (only-in racket/fixnum fx> fx=))
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fixed size integer sets.

(define IntSet (ordset fx> fx=))
(define intset-version (order-version IntSet))
(define intset-make-empty (order-make-empty IntSet))
(define intset-singleton (order-singleton IntSet))
(define intset-add (order-add IntSet))
(define intset (order-set IntSet))
(define intset-size (order-size IntSet))
(define intset-empty? (order-empty? IntSet))
(define intset-equal? (order-equal? IntSet))
(define intset-member? (order-member? IntSet))
(define intset-union (order-union IntSet))
(define intset-difference (order-difference IntSet))
(define intset-intersection (order-intersection IntSet))
(define intset-union-and-note (order-union-and-note IntSet))
(define intset-filter (order-filter IntSet))
(define intset-exists? (order-exists? IntSet))
(define intset-for-each (order-for-each IntSet))
(define intset-map (order-map IntSet))
(define intset-foldl (order-foldl IntSet))
(define intset-min (order-min IntSet))
(define intset-max (order-max IntSet))
(define intset-subset? (order-subset? IntSet))
(define intset->list (order-set->list IntSet))
(define list->intset (order-list->set IntSet))
