module TestQueue
open FStar.Queue

let my_queue = enqueue 3 (enqueue 2 (enqueue 1 empty))

let _ = assert 
  (eq my_queue
      (as_queue [1; 2; 3]))
let _ = assert 
  (eq (enqueue 4 my_queue) 
      (as_queue [1; 2; 3; 4]))
let _ = assert 
  (fst (dequeue my_queue) == 1)
let _ = assert 
  (eq (snd (dequeue my_queue)) 
      (enqueue 3 (enqueue 2 empty)))
let _ = assert 
  (eq (snd (dequeue (enqueue 1 empty))) 
      empty)
let _ = assert 
  (peek my_queue == 1)
let _ = assert 
  (peek (snd (dequeue my_queue)) == 2)