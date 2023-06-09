module FStar.Queue

module L = FStar.List.Tot
open FStar.Seq

(* write comment *)
type queue a = p:(list a & list a){L.isEmpty (fst p) ==> L.isEmpty (snd p)}

(* write comment *)
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

(* write comment *)
let queue_to_seq #a q
	= seq_of_list (queue_to_list q)

(* write comment *)
let queue_of_seq #a s
	= queue_of_list (seq_to_list s)

(* write comment *)
let equal #a q1 q2 = queue_to_seq q1 == queue_to_seq q2

(* write comment *)
let lemma_eq_intro #_ q1 q2 = ()

(* write comment *)
let lemma_eq_elim #_ q1 q2 = ()

let lemma_list_queue_bij (#a:Type) (l:list a) 
	: Lemma (queue_to_list (queue_of_list l) == l)
	= match l with
	  | [] -> ()
	  | _ -> L.append_l_nil l

let lemma_queue_list_bij (#a:Type) (q:queue a) 
	: Lemma (equal (queue_of_list (queue_to_list q)) q)
	= match fst q with
	  | [] -> ()
	  | l -> (
			L.append_l_nil (L.append l (L.rev (snd q)))
		)

(* write comment *)
let lemma_seq_queue_bij (#a:Type) (s:seq a) 
	: Lemma (queue_to_seq (queue_of_seq s) == s) 
  = let l = (seq_to_list s) in
		lemma_list_queue_bij l;
		lemma_seq_list_bij s

(* write comment *)
let lemma_queue_seq_bij (#a:Type) (q:queue a) 
	: Lemma (equal (queue_of_seq (queue_to_seq q)) q) 
	= let l = (queue_to_list q) in
		lemma_queue_list_bij q;
		lemma_list_seq_bij l

(* write comment *)
let enqueue (#a:Type) (x:a) (q:queue a) 
	: queue a
	= match fst q with
	  | [] -> [x], []
	  | l -> l, x :: (snd q)

(* write comment *)
let dequeue (#a:Type) (q:queue a{not_empty q}) 
	: a & queue a
	= lemma_seq_of_list_induction (queue_to_list q);
		let hd :: tl = fst q in
	  match tl with
		| [] -> hd, (L.rev (snd q), [])
	  | _ -> hd, (tl, (snd q))

(* write comment *)
let peek (#a:Type) (q:queue a{not_empty q}) 
	: a
	= lemma_seq_of_list_induction (queue_to_list q);
		L.hd (fst q)

(* write comment *)
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

let rec lemma_append_seq_of_list_dist (#a:Type) (l1 l2:list a) 
	: Lemma (ensures Seq.equal (seq_of_list (L.append l1 l2)) (Seq.append (seq_of_list l1) (seq_of_list l2)))
	= match l1 with 
		| [] -> L.append_nil_l l2
		| hd :: tl -> 
		(
			lemma_seq_of_list_induction (hd :: (L.append tl l2));
			lemma_append_seq_of_list_dist tl l2;
			Seq.append_cons hd (seq_of_list tl) (seq_of_list l2);
			lemma_seq_of_list_induction (hd :: tl)
		)

let lemma_snoc_list_seq (#a:Type) (x:a) (q:queue a)
	: Lemma (seq_of_list (L.snoc ((queue_to_list q),x)) == Seq.snoc (queue_to_seq q) x)
	= let l = (queue_to_list q) in 
		lemma_append_seq_of_list_dist l [x];
		lemma_seq_list_bij (Seq.create 1 x)

(* write comment *)
let lemma_enqueue_ok (#a:Type) (x:a) (q:queue a)
	: Lemma (queue_to_seq (enqueue x q) == Seq.snoc (queue_to_seq q) x)
	= lemma_enqueue_ok_list x q; 
		lemma_snoc_list_seq x q

let lemma_dequeue_ok_list (#a:Type) (q:queue a{not_empty q}) 
	: Lemma (fst (dequeue q) :: queue_to_list (snd (dequeue q)) == queue_to_list q)
	= lemma_seq_of_list_induction (queue_to_list q);
		let hd :: tl = fst q in
	  match tl with
	  | [] -> L.append_l_nil (L.rev (snd q))
	  | _ -> L.append_assoc [hd] tl (L.rev (snd q))
	
let lemma_cons_list_seq (#a:Type) (x:a) (q:queue a)
	: Lemma (seq_of_list (x :: (queue_to_list q)) == Seq.cons x (queue_to_seq q))
	= let l = (queue_to_list q) in
		lemma_append_seq_of_list_dist [x] l;
		lemma_seq_list_bij (Seq.create 1 x)

(* write comment *)
let lemma_dequeue_ok (#a:Type) (q:queue a{not_empty q})
  : Lemma (let hd, tl = dequeue q in
   		hd == Seq.head (queue_to_seq q) /\
   		equal tl (queue_of_seq (Seq.tail (queue_to_seq q))))
	= lemma_dequeue_ok_list q;
		lemma_cons_list_seq (fst (dequeue q)) (snd (dequeue q))

(* write comment *)
let lemma_peek_ok (#a:Type) (q:queue a{not_empty q})
	: Lemma (peek q == Seq.head (queue_to_seq q))
	= lemma_dequeue_ok_list q