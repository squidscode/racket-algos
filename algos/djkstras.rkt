#lang racket

(require test-engine/racket-tests)
(require "../ds/heap.rkt")

(define DEBUG_PRINT #f)
(define dprintf (if DEBUG_PRINT printf values))

; A Node is `Any`
; An Edge is a '(left right) where left and right are Node's
; An AdjPair is (cons node connections)

#; {AdjPairs Edge -> AdjPairs}
; Adds an Edge to the AdjPair list
(define (add-edge pairs edge) 
  (cond 
    [(cons? pairs)  
     (let ([first-pair (first pairs)]
           [rest-of-pairs (rest pairs)])
       (if (equal? (car first-pair) (car edge)) ; if first pair matches
         (cons (add-connection first-pair (second edge)) (rest pairs))
         (cons first-pair (add-edge rest-of-pairs edge))))]
    [(null? pairs) (list (cons (car edge) (list (second edge))))]))

#; {AdjPair Node -> AdjPair}
; Adds the Node to the list of connections in the AdjPair
(define (add-connection pair node)
  (cons (car pair) (cons node (cdr pair))))

#; {Edges -> AdjPairs}
; edges->adg: list[Edge] -> List[[Node, List[Node]]]
(define (edges->adjpairs edges)
  (begin 
    (define (edges->adj-helper pairs edges)
      (cond 
        [(cons? edges)  
         (edges->adj-helper 
           (add-edge pairs (first edges)) 
           (rest edges))]
        [(null? edges) pairs]))
    (edges->adj-helper '() edges)))

#; {AdjPair Node -> Nodes}
; graph-traversal returns an ordering of nodes in the order that they were 
; visited according to the initial, push, in, fst, pop, and lst functions 
; passed in.
(define (graph-traversal adjs start 
 ; Functions on the list of nodes
 ; ds-initial     :: <A>
 ; ds-push        :: { Node <A> -> <A> }
 ; ds-peek        :: { <A> -> Node }
 ; ds-pop         :: { <A> -> <A> }
 ; ds-empty?      :: { <A> -> bool }
 ds-initial ds-push ds-peek ds-pop ds-empty?
 ; Functions on the accumulator (all of these are optional)
 ; acc-initial    :: <B>
 ; acc-push       :: { Node <B> -> <B> }
 ; acc-contains   :: { Node <B> -> bool }
 [acc-initial '()] [acc-push cons] [acc-contains member])
  (let ([ds-not-empty? (negate ds-empty?)] [steps (box 1)])
  (define (help adjs acc nxtlst) 
    (dprintf "------- STEP: ~s -------\n" (unbox steps))
    (set-box! steps (+ 1 (unbox steps)))
    (dprintf "acc: ~s\n" acc)
    (dprintf "nxtlst: ~s\n" 
            (if (and (cons? nxtlst) (heap-node? (car nxtlst))) 
              (cons (heap->list (car nxtlst)) (cdr nxtlst)) 
              nxtlst))
    (cond 
      ; Have we already seen this node?
      [(and (ds-not-empty? nxtlst) (acc-contains (ds-peek nxtlst) acc))
       (help adjs acc (ds-pop nxtlst))]
      ; We have seen this node before!
      [(ds-not-empty? nxtlst)
       (let* ([nxt (ds-peek nxtlst)]
              [rst (ds-pop nxtlst)]
              [out (assoc nxt adjs)]                  ; #f or list[Node]
              [out (if (false? out) '() (rest out))]  ; list[Node]
              [out (filter (negate (curryr member acc)) out)]) 
         (help adjs (acc-push nxt acc) (foldl ds-push rst out)))]
      ; Finished accumulating
      [(ds-empty? nxtlst) (reverse acc)]))
  (help adjs acc-initial (ds-push start ds-initial))))

#; {AdjPair Node -> Nodes}
(define (dfs adjs start) 
  (graph-traversal adjs start '() cons first rest null?))

(define push-back (lambda (x l) (append l (list x))))
(define (bfs adjs start) 
  (graph-traversal adjs start '() push-back first rest null?))

(define (apply-cons f1 f2)
  (lambda (v) (cons (f1 (car v)) (f2 (cdr v)))))

(define (heap-push-and-set-hash weights op node->num new-node heap-and-hash)
  (let*
    ([heap (car heap-and-hash)]
     [hs   (cdr heap-and-hash)])
    (dprintf "heap-push: ~s, weight: ~s\n" new-node (node->num new-node))
    (for-each (lambda (to-and-weight) 
                (let
                  ([to (first to-and-weight)]
                   [weight (second to-and-weight)])
                (hash-set! 
                  hs 
                  to 
                  (min ; the to edge is now the min of the previous + new dest
                    (hash-ref hs to +inf.f)
                    (+ (node->num new-node) weight)))))
              (map rest (filter 
                          (lambda (e) (equal? (first e) new-node))
                          weights)))
    (cons (heap-push op node->num new-node heap) hs)))

#| uncomment for sanity checks:
(heap-push-and-check-hash '((0 1 2)) 0 (cons (heap-leaf) (make-hash)))
(heap-push-and-check-hash '((0 1 2) (0 1 5) (0 2 0)) 
                          0 
                          (cons (heap-leaf) (make-hash)))
|#

; weights: (list from to weight)
(define (djkstras edges op start) 
  (let*
    ([hs (make-hash)]
     [node->num (lambda (node) (hash-ref hs node +inf.f))]
     [adjs (edges->adjpairs (weighted->unweighted edges))])
    (hash-set! hs start 0)
    (values 
      (graph-traversal 
        adjs
        start
        (cons (heap-leaf) hs)
        (curry heap-push-and-set-hash edges op node->num)
        (compose heap-node-val car)
        (lambda (hp-h) 
          (dprintf "heap-pop: ~s\n" ((compose heap-node-val car) hp-h))
          (cons (heap-pop op node->num (car hp-h)) (cdr hp-h)))
        (compose heap-leaf? car)) 
      hs)))


(define (weighted->unweighted edges)
  (map (lambda (p) (list (first p) (second p))) edges))

(check-expect (add-connection (cons 2 '()) 3)
              (cons 2 '(3)))
(check-expect (add-connection (cons 2 '(4)) 3)
              (cons 2 '(3 4)))
(check-expect (add-edge (list (cons 2 '(4))) '(3 4))
              (list (cons 2 '(4)) (cons 3 '(4))))

(define e1 (list 1 2))
(define e2 (list 1 3))
(define e3 (list 3 2))
(define e4 (list 2 4))
(define e5 (list 4 5))

(check-expect (edges->adjpairs (list e1 e2 e3 e4 e5)) 
              '((1 3 2) (3 2) (2 4) (4 5)))
(check-expect (dfs (edges->adjpairs (list e1 e2 e3 e4 e5)) 1)
              '(1 2 4 5 3))
(check-expect (bfs 
                (edges->adjpairs (list e1 e2 e3 e4 e5))
                1)
              '(1 3 2 4 5))

; from, to, weight
(define we1 '(1 2 3))
(define we2 '(1 3 1))
(define we3 '(3 2 1))
(define we4 '(3 4 1))
(define we5 '(4 5 2))

(define w (list we1 we2 we3 we4 we5))
(define w-edges (weighted->unweighted w))
(define w-adj (edges->adjpairs w-edges))

; (djkstras w < 1)

(define (directed->undirected we) 
  (let ([we (remove-duplicates we)])
    (foldl 
      (lambda (l r) (cons (list (second l) (first l) (third l)) r))
      we
      we)))

; https://www.geeksforgeeks.org/dijkstras-shortest-path-algorithm-greedy-algo-7/
(define w2 '((0 1 4) (0 7 8) (1 7 11) (1 2 8) (7 6 1) (7 8 7)
             (2 8 2) (8 6 6) (2 5 4)  (2 3 7) (6 5 2) (3 5 14)
             (3 4 9) (5 4 10)))
; (directed->undirected w2)
(define-values (l m) (djkstras (directed->undirected w2) < 0))
(check-expect l '(0 1 7 6 5 2 8 3 4))
(check-within m 
              (make-hash '((0 . 0) (1 . 4) (2 . 12) (3 . 19) (4 . 21) (5 . 11)
                                   (6 . 9) (7 . 8) (8 . 14)))
              0.01)

