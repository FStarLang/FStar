module FStar.StackArray

//#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Seq
open FStar.StackHeap
open FStar.SST

(* abstract *) type array (t:Type) = ref (seq t)

assume val op_At_Bar: #a:Type -> array a -> array a -> St (array a)

assume val of_seq: #a:Type -> s:seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun s0 x s1 -> (not(contains s0 x)
		             /\ frameOf x = top_frame_id s1
                             /\ contains s1 x
                             /\ modifies !{} s0 s1
                             /\ sel s1 x =s)))

assume val to_seq: #a:Type -> s:array a -> ST (seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> (sel h0 s=x /\ h0==h1)))

val create : #a:Type -> n:nat -> init:a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x)
		             /\ frameOf x = top_frame_id h1
                             /\ contains h1 x
			     /\ stack h1 = stack h0
			     /\ modifies_one (top_frame_id h1) h0 h1
			     /\ modifies_ref (top_frame_id h1) !{asRef x} h0 h1	                    
			     /\ sel h1 x = Seq.create n init
			     )))
let create #a n init = salloc (Seq.create n init)

assume val index : #a:Type -> x:array a -> n:nat -> ST a
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 v h1 -> (n < Seq.length (sel h0 x)
                             /\ h0==h1
                             /\ v=Seq.index (sel h0 x) n)))

assume val upd : #a:Type -> x:array a -> n:nat -> v:a -> ST unit
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 u h1 -> (n < Seq.length (sel h0 x)
                            /\ contains h1 x
			    /\ modifies (Set.singleton (frameOf x)) h0 h1
			    /\ modifies_ref (frameOf x) !{as_ref (refOf x)} h0 h1
                            /\ h1==StackHeap.upd h0 x (Seq.upd (sel h0 x) n v))))

assume val length: #a:Type -> x:array a -> ST nat
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> y=length (sel h0 x) /\ h0==h1))

assume val op: #a:Type -> f:(seq a -> Tot (seq a)) -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures  (fun h0 u h1 -> modifies_ref (frameOf x) !{as_ref (refOf x)} h0 h1 /\ sel h1 x=f (sel h0 x)))

val swap: #a:Type -> x:array a -> i:nat -> j:nat{i <= j} -> ST unit 
  (requires (fun s -> contains s x /\ j < Seq.length (sel s x)))
  (ensures (fun s0 _u s1 ->
    (j < Seq.length (sel s0 x))
    /\ contains s1 x
    /\ (s1==StackHeap.upd s0 x (SeqProperties.swap (sel s0 x) i j))))
let swap #a x i j =
  let h0 = get () in
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj; 
  let h1 = SST.get () in
  let s1 = sel h1 x in 
  cut (b2t(Heap.equal (heapOf x h1) (Heap.upd (heapOf x h0) (as_ref (refOf x)) s1))); 
  cut (Map.equal (heaps h1) (heaps (StackHeap.upd h0 x s1)))

(* Helper functions for stateful array manipulation *)
val copy_aux:
  #a:Type -> s:array a -> cpy:array a -> ctr:nat ->
     ST unit
	(requires (fun h -> (contains h s /\ contains h cpy /\ s <> cpy)
			    /\ (Seq.length (sel h cpy) = Seq.length (sel h s))
			    /\ (ctr <= Seq.length (sel h cpy))
			    /\ (forall (i:nat). i < ctr ==> Seq.index (sel h s) i = Seq.index (sel h cpy) i)))
	(ensures (fun h0 u h1 -> (contains h1 s /\ contains h1 cpy /\ s <> cpy )
			      /\ modifies_one (frameOf cpy) h0 h1
			      /\ (modifies_ref (frameOf cpy) !{as_ref (refOf cpy)} h0 h1)
			      /\ (Seq.equal (sel h1 cpy) (sel h1 s))
			      /\ stack h1 = stack h0))
let rec copy_aux #a s cpy ctr =
  match length cpy - ctr with
  | 0 -> ()
  | _ -> upd cpy ctr (index s ctr);
	 copy_aux s cpy (ctr+1)

val copy:
  #a:Type -> s:array a ->
  ST (array a) 
     (requires (fun h -> contains h s
			 /\ Seq.length (sel h s) > 0))
     (ensures (fun h0 r h1 -> modifies_one (top_frame_id h1) h0 h1
			    /\ modifies_ref (top_frame_id h1) !{asRef s} h0 h1
	                    /\ frameOf r = top_frame_id h1
			    /\ not(contains h0 r)
			    /\ (contains h1 r)
			    /\ (Seq.equal (sel h1 r) (sel h0 s))))
let copy #a s =
  let h0 = get () in
  let cpy = create (length s) (index s 0) in
  let h = get () in
  copy_aux s cpy 0; 
  let h1 = get () in
  cpy

val blit_aux:
  #a:Type -> s:array a -> s_idx:nat -> t:array a -> t_idx:nat -> len:nat -> ctr:nat ->
  ST unit
     (requires (fun h ->
		(contains h s /\ contains h t /\ s <> t)
		/\ (Seq.length (sel h s) >= s_idx + len)
		/\ (Seq.length (sel h t) >= t_idx + len)
		/\ (ctr <= len)
		/\ (forall (i:nat).
		    i < ctr ==> Seq.index (sel h s) (s_idx+i) = Seq.index (sel h t) (t_idx+i))))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ stack h1 = stack h0
	       /\ (modifies (Set.singleton (frameOf t)) h0 h1)
	       /\ (modifies_ref (frameOf t) !{asRef t} h0 h1)
	       /\ (Seq.length (sel h1 s) >= s_idx + len)
	       /\ (Seq.length (sel h1 t) >= t_idx + len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (forall (i:nat).
		   i < len ==> Seq.index (sel h1 s) (s_idx+i) = Seq.index (sel h1 t) (t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < t_idx \/ i >= t_idx + len)) ==>
		     Seq.index (sel h1 t) i = Seq.index (sel h0 t) i) ))
let rec blit_aux #a s s_idx t t_idx len ctr =
  let h0 = get() in
  match len - ctr with
  | 0 -> ()
  | _ -> upd t (t_idx + ctr) (index s (s_idx + ctr));
	 let h = get() in
	 cut (b2t(Heap.equal (heapOf t h) (Heap.upd (heapOf t h0) (asRef t) (sel h t)))); 
	 cut (Map.equal (heaps h) (heaps (StackHeap.upd h0 t (sel h t)))); 
	 cut (sel h t = Seq.upd (sel h0 t) (t_idx+ctr) (Seq.index (sel h0 s) (s_idx+ctr))); 
	 cut (forall (i:nat). i < ctr+1 ==> Seq.index (sel h0 s) (s_idx+i) = Seq.index (sel h t) (t_idx+i));
	 assert(s <> t);
	 blit_aux s s_idx t t_idx len (ctr+1)
	 
val blit:
  #a:Type -> s:array a -> s_idx:nat -> t:array a -> t_idx:nat -> len:nat ->
  ST unit
     (requires (fun h ->
		(contains h s)
		/\ (contains h t)
		/\ (s <> t)
		/\ (Seq.length (sel h s) >= s_idx + len)
		/\ (Seq.length (sel h t) >= t_idx + len)))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ stack h1 = stack h0
	       /\ (Seq.length (sel h1 s) >= s_idx + len)
	       /\ (Seq.length (sel h1 t) >= t_idx + len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (modifies_one (frameOf t) h0 h1)
	       /\ (modifies_ref (frameOf t) !{asRef t} h0 h1)
	       /\ (forall (i:nat).
		   i < len ==> Seq.index (sel h1 s) (s_idx+i) = Seq.index (sel h1 t) (t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < t_idx \/ i >= t_idx + len)) ==>
		     (Seq.index (sel h1 t) i = Seq.index (sel h0 t) i)) ))
let rec blit #a s s_idx t t_idx len =
  blit_aux s s_idx t t_idx len 0

val sub :
  #a:Type -> s:array a -> idx:nat -> len:nat ->
  ST (array a)
    (requires (fun h ->
      (contains h s)
      /\ (Seq.length (sel h s) > 0)
      /\ (idx + len <= Seq.length (sel h s))))
    (ensures (fun h0 t h1 ->
      (contains h1 t)
      /\ (contains h0 s)
      /\ not(contains h0 t)
      /\ modifies_one (top_frame_id h1) h0 h1
      /\ modifies_ref (top_frame_id h1) !{asRef t} h0 h1
      /\ frameOf t = top_frame_id h1
      /\ (Seq.length (sel h0 s) > 0)
      /\ (idx + len <= Seq.length (sel h0 s))
      /\ (Seq.equal (Seq.slice (sel h0 s) idx (idx+len)) (sel h1 t))))
let sub #a s idx len =
  let t = create len (index s 0) in
  blit s idx t 0 len;
  t
