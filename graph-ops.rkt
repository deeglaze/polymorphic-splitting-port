#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Transpose, Depth First Search, Strongly Connected Components,
;; Transitive Closure for graphs.

(require racket/mpair)
(provide scc transitive)

;; Given a graph G as a list of nodes and a function that maps a node
;; to its children, return a children function for the transpose of G.
(define transpose
  (lambda (G children)
    (let* ([Gt '()]
           (new-node
             (lambda (node)
               (or (massq node Gt)
                   (let ((c (mcons node '())))
                     (set! Gt (mcons c Gt))
                     c)))))
      (mfor-each
        (lambda (node)
          (new-node node)
          (mfor-each
            (lambda (child)
              (let ((c (new-node child)))
                (unless (mmemq node (mcdr c))
                  (set-mcdr! c (mcons node (mcdr c))))))
            (children node)))
        G)
      (lambda (node)
        (mcdr (massq node Gt))))))

;; Given a graph G as a list of nodes and a function that maps a node
;; to its children, return a depth first forest of G as a list of
;; nodes in order of finishing time.
(define dfs
  (lambda (G children)
    (define visited '())
    (define (dfs-tree node)
      (define finished '())
      (let dfs ([node node])
        (unless (mmemq node visited)
          (set! visited (mcons node visited))
          (mfor-each dfs (children node))
          (set! finished (mcons node finished))))
      finished)
    (for/fold ([acc '()]) ([node (in-mlist G)])
      (define tree (dfs-tree node))
      (cond [(null? tree) acc]
            [else (mappend! acc (mlist (mreverse! tree)))]))))

;; (used by components)
;; Given a graph G as a list of nodes and a function that maps a node
;; to its children, return a list of its strongly connected components.
(define scc
  (lambda (G children)
    (let* ([finish (for/fold ([acc '()])
                       ([node (in-mlist (dfs G children))])
                     (mappend! acc node))]
           [t-children (transpose G children)])
      (dfs (mreverse! finish) t-children))))

;; (used by used-before)
;; Given a graph G as a list of nodes and a function that maps a node
;; to its children, return a children function representing the
;; transitive (but not necessarily reflexive) closure of G.
(define (transitive G children)
  (lambda (node)
    (define node* '())
    (define (search node)
      (unless (memq node node*)
        (set! node* (cons node node*))
        (for-each search (children node))))
    (for-each search (children node))
    node*))
