module TestQueue

open FStar.Queue
open FStar.Seq

let my_queue = enqueue 3 (enqueue 2 (enqueue 1 Queue.empty))
let my_seq = Seq.cons 1 (Seq.cons 2 (Seq.cons 3 Seq.empty))

// let _ = assert 
//   (eq my_queue (queue_of_seq my_seq))
// let _ = assert 
//   (eq (enqueue 4 my_queue) 
//       (queue_of_seq (Seq.snoc my_queue 4)))
// let _ = assert 
//   (fst (dequeue my_queue) == 1)
// let _ = assert 
//   (eq (snd (dequeue my_queue)) 
//       (enqueue 3 (enqueue 2 empty)))
// let _ = assert 
//   (eq (snd (dequeue (enqueue 1 empty))) 
//       empty)
let _ = assert 
  (peek my_queue == 1)
// let _ = assert 
//   (peek (snd (dequeue my_queue)) == 2)