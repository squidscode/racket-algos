#lang racket

(require test-engine/racket-tests)

(provide 
  heap-leaf 
  heap-push
  heap-pop
  heap-node-val
  heap-leaf?
  heap-node? 
  heap->list
  list->heap)

(struct heap-node [val depth size left right] #:transparent
  #:guard (lambda (v d s l r name) 
            (unless (= d (+ (max (heap-depth l) (heap-depth r)) 1))
              (error (string->symbol (format "make-~a" name))
                     "depth must be max(lft, rgt) + 1"))
            (unless (<= (abs (- (heap-depth l) (heap-depth r))) 1)
              (error (string->symbol (format "make-~a" name))
                     "depth on left and right must have at most a difference of one"))
            (unless (>= (heap-depth l) (heap-depth r))
              (error (string->symbol (format "make-~a" name))
                     "depth on left must be >= depth on right"))
            (unless (= (+ (heap-size l) (heap-size r) 1) s)
              (error (string->symbol (format "make-~a" name))
                     "node size is not l + r"))
            (values v d s l r)))
(struct heap-leaf [] #:transparent)

(define (heap-depth heap) 
  (if (heap-node? heap) (heap-node-depth heap) 0))

(define (heap-size heap) 
  (if (heap-node? heap) (heap-node-size heap) 0))

(define h1 (heap-node 10 1 1 (heap-leaf) (heap-leaf)))
(define h2 (heap-node 12 2 3 h1 h1))
(define h3 (heap-node 14 3 7 h2 h2))

(check-expect (heap-depth h3) 3)
(check-expect (heap-depth h2) 2)
(check-expect (heap-depth (heap-leaf)) 0)

#; { List -> Heap }
; 0 -> 1,2, 1 -> 3,4
; 2(3+1)-1 = 2*3 + 1
(define (list->heap lst) 
  (define n (length lst))
  (define (list->heap i) 
    (cond 
      [(< i n) 
       (let*
         ([hl (list->heap (- (* 2 (+ i 1)) 1))]
          [hr (list->heap (* 2 (+ i 1)))]
          [d (+ (heap-depth hl) 1)]
          [sz (+ 1 (heap-size hl) (heap-size hr))])
         (heap-node (list-ref lst i) d sz hl hr))]
      [else (heap-leaf)]))
  (list->heap 0))

#; { Heap -> List }
(define (heap->list heap)
  (define (heap->list heap depth)
    (cond
      [(heap-leaf? heap) '()]
      [(= 0 depth) (list heap)]
      [else (append (heap->list (heap-node-left heap) (- depth 1))
                    (heap->list (heap-node-right heap) (- depth 1)))]))
  ; (flatten (map heap-node-val (heap->list heap X)))
  (flatten (map (compose (curry map heap-node-val) (curry heap->list heap)) 
                (range 0 (heap-depth heap)))))

(define heap-list-identity (compose heap->list list->heap))

(check-expect (heap-list-identity '()) '())
(check-expect (heap-list-identity '(1)) '(1))
(check-expect (heap-list-identity '(1 2)) '(1 2))
(check-expect (heap-list-identity '(1 2 3)) '(1 2 3))
(check-expect (heap-list-identity '(1 2 3 4 5 6 7 8)) '(1 2 3 4 5 6 7 8))

#; { Heap -> List[Node] }
; child->root path
(define (heap->child-root-path heap [acc '()])
  (cond 
    [(heap-node? heap) 
     (let ([lft (heap-depth (heap-node-left heap))]
           [rgt (heap-depth (heap-node-right heap))])
       (heap->child-root-path 
         ((if (> lft rgt) heap-node-left heap-node-right) heap)
         (cons heap acc)))]
    [(heap-leaf? heap) acc]))

(check-expect (map heap->list (heap->child-root-path (list->heap '(1 2 3 4 5))))
              '((5) (2 4 5) (1 2 3 4 5)))

(define (heap-node->num node->num heap)
  (node->num (heap-node-val heap)))

#; { HeapNode HeapNode -> HeapNode }
; Swaps the inner values of the parent and the child
(define (swap parent child)
  (let* 
    ([vchild (heap-node-val child)]
     [dchild (heap-node-depth child)]
     [lchild (heap-node-left child)]
     [rchild (heap-node-right child)]
     [vparent (heap-node-val parent)]
     [sz (+ 1 (heap-size lchild) (heap-size rchild))]
     [new-child (heap-node vparent dchild sz lchild rchild)]
     [lparent (if (eq? (heap-node-left parent) child) 
                new-child 
                (heap-node-left parent))]
     [rparent (if (eq? (heap-node-right parent) child)
                new-child
                (heap-node-right parent))]
     [sz (+ 1 (heap-size lparent) (heap-size rparent))])
    (heap-node vchild (heap-node-depth parent) sz lparent rparent)))

(define h (list->heap '(1 2 3 4 5)))
(check-expect (heap->list (swap h (heap-node-left h))) '(2 1 3 4 5))
(check-expect (heap->list (swap h (heap-node-right h))) '(3 2 1 4 5))

#; { HeapNode HeapNode HeapNode -> HeapNode }
; Given parent, previous child, and new child, create a new parent with 
; where the new child replaces the previous child
(define (replace-parent parent pchild nchild)
  (let*  
    ([vparent (heap-node-val parent)]
     [lparent (if (eq? (heap-node-left parent) pchild)
                nchild
                (heap-node-left parent))]
     [rparent (if (eq? (heap-node-right parent) pchild)
                nchild
                (heap-node-right parent))]
     [dparent (+ 1 (max (heap-depth lparent) (heap-depth rparent)))]
     [sz (+ 1 (heap-size lparent) (heap-size rparent))])
    (heap-node vparent dparent sz lparent rparent)))

(check-expect 
  (heap->list (replace-parent h (heap-node-left h) (heap-node-right h)))
  '(1 3 3))
(check-expect 
  (heap->list (replace-parent h (heap-node-right h) (heap-node-left h)))
  '(1 2 2 4 5 4 5))

#; { Heap -> Heap }
; Assume the node we want to upheap is in the `insert position` i.e. is the 
; bottom-most, left-most node in the binary heap.
(define (upheap op node->num heap) 
  #; { List[HeapNode] -> Heap }
  ; Given a list of heap-nodes from the leaf to the root, returns a valid heap
  (define (upheap-help leaf->root)
    (cond 
      [(= (length leaf->root) 0) (heap-leaf)]
      [(= (length leaf->root) 1) (first leaf->root)]
      [(op (heap-node->num node->num (second leaf->root))
           (heap-node->num node->num (first leaf->root)))
       (last leaf->root)]
      [(= (length leaf->root) 2) (swap (second leaf->root) (first leaf->root))]
      [(>= (length leaf->root) 3) 
       (let* 
         ([fst (first leaf->root)] 
          [snd (second leaf->root)]
          [thr (third leaf->root)]
          [rst (drop leaf->root 3)]
          [new-snd (swap snd fst)]
          [new-thr (replace-parent thr snd new-snd)])
         (upheap-help (list* new-snd new-thr rst)))]))

  ; Call to inner upheap helper with the leaf->root 
  (let ([leaf->root (heap->child-root-path heap)])
    (upheap-help leaf->root)))

(check-expect (heap->list (upheap < identity (list->heap '(1 2 3 4 0))))
              '(0 1 3 4 2))
(check-expect (heap->list (upheap < identity (list->heap '(1 2 3 4 1))))
              '(1 1 3 4 2))
(check-expect (heap->list (upheap < identity (list->heap '(1 2 3 4 5))))
              '(1 2 3 4 5))

#; { Operation {Value -> Num} Heap -> Heap }
; Assume the node we want to downheap is the top-most node in the binary heap
(define (downheap op node->num heap)
  (define (should-be-bubbled-down? heap fn)
    (cond
      [(heap-leaf? (fn heap)) #false]
      [else (and (heap-node? (fn heap)) 
                 (op (node->num (heap-node-val (fn heap)))
                     (node->num (heap-node-val heap))))]))
  (define (downheap-help root)
    (cond
      [(= (heap-depth root) 0) (heap-leaf)]
      [(= (heap-depth root) 1) root]
      [(not (or (should-be-bubbled-down? root heap-node-left)
                (should-be-bubbled-down? root heap-node-right)))
       root]
      [(heap-leaf? (heap-node-right root))
       (if (op (node->num (heap-node-val (heap-node-left root))) 
               (node->num (heap-node-val root)))
         (swap root (heap-node-left root))
         root)]
      [(>= (heap-depth root) 2)
       (let*
         ([fst root]
          [rgtv (heap-node-val (heap-node-right root))]
          [lftv (heap-node-val (heap-node-left root))]
          [move-right-up? (op (node->num rgtv) (node->num lftv))]
          [r-or-l-fn (if move-right-up? heap-node-right heap-node-left)]
          [lr (r-or-l-fn fst)]
          [new-fst (swap fst lr)]
          [oldn (r-or-l-fn new-fst)]
          [newn (downheap-help oldn)])
         (replace-parent new-fst oldn newn))]))

  (downheap-help heap))

(check-expect (heap->list (downheap < identity (list->heap '(4 1 2 3 5))))
              '(1 3 2 4 5))
(check-expect (heap->list (downheap < identity (list->heap '(1 2 3 4 5))))
              '(1 2 3 4 5))
(check-expect (heap->list (downheap < identity (list->heap '(2 2 3 4 5))))
              '(2 2 3 4 5))
(check-expect (heap->list (downheap < identity (list->heap '(5 2))))
              '(2 5))

(define (is-heap-full? heap)
  (and (= (heap-size heap) (- (expt 2 (heap-depth heap)) 1))))

#; { Operation Node->Num Node Heap -> Heap }
(define (heap-push op node->num node heap)
  #; { Node Heap -> Heap }
  (define (insert-at-end node heap) 
    (cond
      [(heap-leaf? heap) (heap-node node 1 1 (heap-leaf) (heap-leaf))]
      [(heap-node? heap) 
       (let
         ([f (cond 
               [(is-heap-full? heap) heap-node-left] 
               [(is-heap-full? (heap-node-left heap)) heap-node-right]
               [else heap-node-left])])
         (replace-parent heap (f heap) (insert-at-end node (f heap))))]))
  (let*
    ([new-heap (insert-at-end node heap)])
    (upheap op node->num new-heap)))

(check-expect (heap->list (heap-push < identity 1 (list->heap '())))
              '(1))
(check-expect (heap->list (heap-push < identity 2 (list->heap '(1))))
              '(1 2))
(check-expect (heap->list (heap-push < identity 1 (list->heap '(2))))
              '(1 2))
(check-expect (heap->list (heap-push < identity 1 (list->heap '(2 3 4 5))))
              '(1 2 4 5 3))
(check-expect (heap->list (heap-push < identity 2 (list->heap '(1 3 4 5))))
              '(1 2 4 5 3))
(check-expect (heap->list (heap-push < identity 3 (list->heap '(1 2 4 5))))
              '(1 2 4 5 3))

#; {Heap Value -> Heap}
(define (replace-value heap val)
  (cond
    [(heap-leaf? heap) heap]
    [(heap-node? heap) 
     (heap-node
       val
       (heap-node-depth heap)
       (heap-node-size heap)
       (heap-node-left heap)
       (heap-node-right heap))]))

#; {Heap -> Bool}
(define (is-last-heap-node? heap) 
  (and (heap-node? heap) 
       (heap-leaf? (heap-node-left heap)) 
       (heap-leaf? (heap-node-right heap))))

#; { Heap -> Heap }
(define (heap-pop op node->num heap)
  #; {Heap -> Heap Node}
  (define (pop-last heap)
    (cond
      [(heap-leaf? heap) (error "Pop last should not be called on an empty heap")]
      [(and (heap-node? heap) (is-last-heap-node? heap))
       (values (heap-leaf) heap)]
      [(heap-node? heap)
       (let*-values
         ([(f) (cond 
               [(is-heap-full? heap) heap-node-right]
               [(not (is-heap-full? (heap-node-right heap))) heap-node-right]
               [else heap-node-left])]
          [(new-heap popped-node) (pop-last (f heap))])
         (values (replace-parent heap (f heap) new-heap) popped-node))]))
  (let*-values 
    ([(new-heap popped-node) (pop-last heap)]
     [(new-heap) (replace-value new-heap (heap-node-val popped-node))])
    (downheap op node->num new-heap)))

(check-expect (heap->list (heap-pop < identity (list->heap '(1))))
              '())
(check-expect (heap->list (heap-pop < identity (list->heap '(1 2 3 4))))
              '(2 4 3))
(check-expect (heap->list (heap-pop < identity (list->heap '(1 3 2))))
              '(2 3))
(check-expect (heap->list (heap-pop > identity (list->heap '(1 3 2))))
              '(3 2))
(check-expect (heap->list (heap-pop < identity (list->heap '(2 2 7 4 5))))
              '(2 4 7 5))
