module FStar.Queue

open FStar.List.Tot

val queue (a:Type u#a) : Type u#a

val empty (#a:Type) : queue a

val as_list (#a:Type) (q:queue a) : list a

val as_queue (#a:Type) (l:list a) : queue a

val equal (#a:Type) (q1 q2:queue a) : prop

val lemma_eq_intro: #a:Type -> q1:queue a -> q2:queue a -> Lemma
  (requires (as_list q1 == as_list q2))
  (ensures (equal q1 q2))
  [SMTPat (equal q1 q2)]

val lemma_eq_elim: #a:Type -> q1:queue a -> q2:queue a -> Lemma
  (requires (equal q1 q2))
  (ensures q1 == q2)
  [SMTPat (equal q1 q2)]

let not_empty (#a:Type) (q:queue a) : prop
  = ~(as_list q == [])

val lemma_as_list_as_queue_inv: #a:Type -> l:list a -> Lemma
  (as_list (as_queue l) == l) 
  [SMTPat (as_queue l)]

val lemma_as_queue_as_list_inv: #a:Type -> q:queue a -> Lemma
  (as_queue (as_list q) == q) 
  [SMTPat (as_list q)]

val enqueue (#a:Type) (x:a) (q:queue a) : queue a

val dequeue (#a:Type) (q:queue a{not_empty q}) : a & queue a

val peek (#a:Type) (q:queue a{not_empty q}) : a

val lemma_empty_ok: #a:Type -> Lemma
  (as_list #a empty == [])
  [SMTPat (empty #a)]

val lemma_enqueue_ok: #a:Type -> x:a -> q:queue a -> Lemma
  (as_list (enqueue x q) == append (as_list q) [x]) 
  [SMTPat (enqueue x q)]

val dequeue_ok: #a:Type -> q:queue a{not_empty q} -> Lemma
  ((fst (dequeue q) :: as_list (snd (dequeue q))) == as_list q)
  [SMTPat (dequeue q)]

val peek_ok: #a:Type -> q:queue a{not_empty q} -> Lemma
  (peek q == hd (as_list q))
  [SMTPat (peek q)]