module FStar.Queue

open FStar.List.Tot

type queue a = p:(list a & list a){isEmpty (fst p) ==> isEmpty (snd p)}

let empty #a = [], []

let as_list #a q
	= match (fst q) with
		| [] -> []
		| _ -> append (fst q) (rev (snd q))

let as_queue #a l
	= match l with 
		| [] -> empty
		| _ -> l, []

let equal #a q1 q2 = as_list q1 == as_list q2

let lemma_eq_intro #_ q1 q2 = ()

let lemma_eq_elim #_ q1 q2 = admit()

let lemma_as_list_as_queue_inv (#a:Type) (l:list a) 
	: Lemma (as_list (as_queue l) == l)
	= match l with
	  | [] -> ()
	  | _ -> append_l_nil l

let lemma_as_queue_as_list_inv (#a:Type) (q:queue a) 
	: Lemma (as_queue (as_list q) == q)
	= match fst q with
	  | [] -> ()
	  | l -> (
		append_l_nil (append l (rev (snd q))); 
		lemma_eq_intro (as_queue (as_list q)) q
		)

let enqueue (#a:Type) (x:a) (q:queue a) 
	: queue a
	= match fst q with
	  | [] -> [x], []
	  | l -> l, x :: (snd q)

let dequeue (#a:Type) (q:queue a{not_empty q}) 
	: a & queue a
	= let hd :: tl = fst q in
	  match tl with
		| [] -> hd, (rev (snd q), [])
	  | _ -> hd, (tl, (snd q))

let peek (#a:Type) (q:queue a{not_empty q}) 
	: a
	= hd (fst q)

let lemma_empty_ok (#a:Type) 
	: Lemma (as_list #a empty == [])
	= ()

let lemma_enqueue_ok (#a:Type) (x:a) (q:queue a) 
	: Lemma (as_list (enqueue x q) == append (as_list q) [x])
	= match fst q with
	  | [] -> ()
	  | l -> (
		append_assoc l (rev (snd q)) [x]; 
		rev_append [x] (snd q)
	  )

let lemma_dequeue_ok (#a:Type) (q:queue a{not_empty q}) 
	: Lemma (as_list q == (fst (dequeue q)) :: as_list (snd (dequeue q)))
	= let hd :: tl = fst q in
	  match tl with
	  | [] -> append_l_nil (rev (snd q))
	  | _ -> append_assoc [hd] tl (rev (snd q))

let lemma_peek_ok (#a:Type) (q:queue a{not_empty q})
	: Lemma (hd (as_list q) == peek q)
	= ()