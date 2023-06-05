module TestQueue
open FStar.Queue

let my_empty = as_queue []
let my_queue = as_queue [1]
let my_queue2 = as_queue #int [1; 2; 3]

// let lemma_my_queue_not_empty : #a:Type -> Lemma (not_empty my_queue) = admit()

#push-options "--print_implicits --print_universes --query_stats"
let _ = assert (empty #bool == my_empty)
let _ = assert (empty #int == my_empty)
let _ = assert (equal (enqueue 2 my_queue) (as_queue [1; 2]))
let _ = assert (dequeue my_queue == 1, as_queue [2; 3])
let _ = assert (dequeue (enqueue 1 my_empty) == 1, my_empty)
let _ = assert (peek my_queue == 1)
let _ = assert (peek (snd (dequeue my_queue)) == 2)