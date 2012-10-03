#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simple FIFO queues.

(provide (struct-out Queue)
         queue-make-empty
         queue-empty?
         queue-push!
         queue-pop!
         queue-memq
         queue-size
         queue->list
         list->queue)

(struct Queue (n in out) #:mutable)

(define queue-make-empty
  (lambda ()
    (Queue 0 '() '())))

(define queue-push!
  (lambda (x q)
    (set-Queue-n! q (+ (Queue-n q) 1))
    (set-Queue-in! q (cons x (Queue-in q)))))

(define queue-empty?
  (lambda (q)
    (= 0 (Queue-n q))))

(define queue-pop!
  (lambda (q)
    (when (queue-empty? q)
      (error 'pop-queue! "Queue is empty"))
    (set-Queue-n! q (- (Queue-n q) 1))
    (when (null? (Queue-out q))
      (set-Queue-out! q (reverse (Queue-in q)))
      (set-Queue-in! q '()))
    (let ((x (car (Queue-out q))))
      (set-Queue-out! q (cdr (Queue-out q)))
      x)))

(define queue-memq
  (lambda (x q)
    (or (memq x (Queue-in q)) (memq x (Queue-out q)))))

(define queue-size Queue-n)

(define queue->list
  (lambda (q)
    (append (Queue-in q) (reverse (Queue-out q)))))

(define list->queue
  (lambda (l)
    (Queue (length l) l '())))
