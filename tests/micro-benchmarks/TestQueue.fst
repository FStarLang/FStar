module TestQueue

module Q = FStar.Queue
open FStar.Queue
open FStar.Seq

let my_queue = enqueue 3 (enqueue 2 (enqueue 1 Q.empty))
let my_seq = Seq.cons 1 (Seq.cons 2 (Seq.cons 3 Seq.empty))

let _ = assert 
  (Q.eq my_queue (queue_of_seq my_seq))
let _ = assert 
  (Q.eq (enqueue 4 my_queue) 
        (queue_of_seq (Seq.snoc my_seq 4)))
let _ = assert 
  (fst (dequeue my_queue) == 1)
let _ = assert 
  (Q.eq (snd (dequeue my_queue)) 
        (enqueue 3 (enqueue 2 Q.empty)))
let _ = assert 
  (Q.eq (snd (dequeue (enqueue 1 Q.empty))) 
        Q.empty)
let _ = assert 
  (peek my_queue == 1)
let _ = assert 
  (peek (snd (dequeue my_queue)) == 2)