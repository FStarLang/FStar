module FStar.Queue

module L = FStar.List.Tot
open FStar.Seq

type queue a = p:(list a & list a){L.isEmpty (fst p) ==> L.isEmpty (snd p)}

let empty #a = [], []

val queue_to_list (#a:Type) (q:queue a) : list a
let queue_to_list #a q
	= match (fst q) with
		| [] -> []
		| _ -> (fst q) @ (L.rev (snd q))

val queue_of_list (#a:Type) (l:list a) : queue a
let queue_of_list #a l
	= match l with 
		| [] -> empty
		| _ -> l, []

let queue_to_seq #a q
	= seq_of_list (queue_to_list q)

let queue_of_seq #a s
	= queue_of_list (seq_to_list s)

let eq #a q1 q2 = queue_to_seq q1 == queue_to_seq q2

let lemma_eq_intro #_ q1 q2 = ()

let lemma_eq_elim #_ q1 q2 = ()

let lemma_list_queue_bij (#a:Type) (l:list a) 
	: Lemma (queue_to_list (queue_of_list l) == l)
	= match l with
	  | [] -> ()
	  | _ -> L.append_l_nil l

let lemma_queue_list_bij (#a:Type) (q:queue a) 
	: Lemma (eq (queue_of_list (queue_to_list q)) q)
	= match fst q with
	  | [] -> ()
	  | l -> (
			L.append_l_nil (L.append l (L.rev (snd q)))
		)

let lemma_seq_queue_bij (#a:Type) (s:seq a) 
	: Lemma (queue_to_seq (queue_of_seq s) == s) 
  = let l = (seq_to_list s) in
		lemma_list_queue_bij l;
		lemma_seq_list_bij s

let lemma_queue_seq_bij (#a:Type) (q:queue a) 
	: Lemma (eq (queue_of_seq (queue_to_seq q)) q) 
	= let l = (queue_to_list q) in
		lemma_queue_list_bij q;
		lemma_list_seq_bij l

let lemma_seq_to_list_empty (#a:Type) (s:seq a)
	: Lemma (s == Seq.empty ==> seq_to_list s == [])
	= lemma_list_seq_bij (seq_to_list s)

let enqueue (#a:Type) (x:a) (q:queue a) 
	: queue a
	= match fst q with
	  | [] -> [x], []
	  | l -> l, x :: (snd q)

let dequeue (#a:Type) (q:queue a{not_empty q}) 
	: a & queue a
	= lemma_seq_to_list_empty (queue_to_seq q);
		let hd :: tl = fst q in
	  match tl with
		| [] -> hd, (L.rev (snd q), [])
	  | _ -> hd, (tl, (snd q))

let peek (#a:Type) (q:queue a{not_empty q}) 
	: a
	= lemma_seq_to_list_empty (queue_to_seq q);
		L.hd (fst q)

let lemma_empty_ok (#a:Type)
	: Lemma (queue_to_seq #a empty == Seq.empty)
  = lemma_seq_list_bij #a Seq.empty

let lemma_enqueue_ok_list (#a:Type) (x:a) (q:queue a) 
	: Lemma (queue_to_list (enqueue x q) == L.snoc ((queue_to_list q),x))
	= match fst q with
	  | [] -> ()
	  | l -> (
		L.append_assoc l (L.rev (snd q)) [x]; 
		L.rev_append [x] (snd q)
	  )

let lemma_snoc_list_seq (#a:Type) (x:a) (q:queue a)
	: Lemma (seq_of_list (L.snoc ((queue_to_list q),x)) == Seq.snoc (queue_to_seq q) x)
	= admit()

let lemma_enqueue_ok (#a:Type) (x:a) (q:queue a)
	: Lemma (queue_to_seq (enqueue x q) == Seq.snoc (queue_to_seq q) x)
	= lemma_enqueue_ok_list x q; 
		lemma_snoc_list_seq x q

let lemma_dequeue_ok_list (#a:Type) (q:queue a{not_empty q}) 
	: Lemma (fst (dequeue q) :: queue_to_list (snd (dequeue q)) == queue_to_list q)
	= lemma_seq_to_list_empty (queue_to_seq q);
		let hd :: tl = fst q in
	  match tl with
	  | [] -> L.append_l_nil (L.rev (snd q))
	  | _ -> L.append_assoc [hd] tl (L.rev (snd q))

let lemma_cons_list_seq (#a:Type) (x:a) (q:queue a)
	: Lemma (seq_of_list (x :: (queue_to_list q)) == Seq.cons x (queue_to_seq q))
	= admit()

let lemma_dequeue_ok (#a:Type) (q:queue a{not_empty q})
  : Lemma (Seq.cons (fst (dequeue q)) (queue_to_seq (snd (dequeue q))) == queue_to_seq q)
	= lemma_dequeue_ok_list q; 
		lemma_cons_list_seq (fst (dequeue q)) (snd (dequeue q))

let lemma_peek_ok (#a:Type) (q:queue a{not_empty q})
	: Lemma (peek q == index (queue_to_seq q) 0)
	= lemma_dequeue_ok_list q