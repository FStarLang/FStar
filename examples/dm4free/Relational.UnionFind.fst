module Relational.UnionFind

open FStar.Seq
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

type id (n:nat) = i:nat{i < n}

type elt (n:nat) = id n * id n

type uf_forest (n:nat) = s:seq (ref (elt n)){length s = n}

(* liveness and separation condition for the forest *)
let live (#n:nat) (uf:uf_forest n) (h:heap) :Type0 =
  (forall (i:id n).{:pattern addr_of (index uf i)} forall (j:id n).{:pattern addr_of (index uf j)}
               i <> j ==> addr_of (index uf i) <> addr_of (index uf j)) /\  //all the refs in the forest are distinct
  (forall (i:id n).{:pattern (h `contains_a_well_typed` (index uf i))}
               h `contains_a_well_typed` (index uf i))  //all the refs in the forest are well typed

(* helpers for getting the parent and height *)
unfold let parent (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot (id n) = fst (sel h (index uf i))
unfold let height (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot (id n) = snd (sel h (index uf i))

(*
 * well-formed conditions on the forest, essentially the invariants needed for proving the termination of operations
 * TODO: add the pattern, perhaps {:pattern (sel h (index uf i))}?
 *)
let well_formed (#n:nat) (uf:uf_forest n) (h:heap) =
  forall (i:id n).{:pattern (sel h (index uf i))}
             (parent uf i h = i \/ height uf i h < height uf (parent uf i h) h)

(*
 * the postcondition parent uf r h1 = r is added because of merge, see below in comments
 *)
reifiable let rec find (#n:nat) (uf:uf_forest n) (i:id n) (ghost_heap:heap)
  :ST (id n) (requires  (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
              (ensures   (fun h0 r h1 -> h0 == h1 /\ parent uf r h1 = r))
	      (decreases (length uf - height #n uf i ghost_heap))
  = let (p, _) = read (index uf i) in
    if p = i then i
    else begin
      find uf p ghost_heap
    end      

reifiable let rec merge (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n)
  : ST unit (requires (fun h0      -> live uf h0 /\ well_formed uf h0))
            (ensures  (fun h0 _ h1 -> live uf h1 /\ well_formed uf h1))
  = let h0 = STATE?.get () in

    let r_1 = find uf i_1 (STATE?.get ()) in
    let r_2 = find uf i_2 (STATE?.get ()) in

    let ref_1 = index uf r_1 in
    let ref_2 = index uf r_2 in

    let _, d_1 = !ref_1 in
    let _, d_2 = !ref_2 in

    assume (d_1 + 1 < length uf);

    if r_1 = r_2 then ()
    else begin
      write ref_1 (r_2, d_1);
      if d_1 + 1 > d_2 then
        //after this write, in order to establish the third clause of well_formed,
	//we need to reason that height of r2's parent is more than d1 + 1, or that r2's parent is r2 itself
	//but we obtained r2 by calling find, so the clause parent uf r h1 = r, is added so that this can go through
        write ref_2 (r_2, d_1 + 1)
    end

reifiable let rec find_opt (#n:nat) (uf:uf_forest n) (i:id n) (ghost_heap:heap)
  :ST (id n) (requires (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
             (ensures  (fun h0 r h1 -> live uf h1 /\ well_formed uf h1 /\ parent uf r h1 = r /\  //these are from find
	                            (r = i \/ height uf r h1 > height uf i h1) /\  //we need this because when we write p' as i's parent
				                                                   //we need to ensure wellformedness i.e. height of p'
										   //is more than the height of i
				     (forall (j:id n).{:pattern (sel h1 (index uf j))} height uf j h0 < height uf i h0 ==>
	                                          sel h1 (index uf j) = sel h0 (index uf j))))  //this last clause to say that i remains unchanged in the recursive call, else when we write its height to be d, we have trouble proving that p's height is more than d
	      (decreases (length uf - height #n uf i ghost_heap))
  = let (p, d) = read (index uf i) in
    if p = i then i
    else
      let h = STATE?.get () in
      let p' = find_opt uf p h in
      write (index uf i) (p', d);
      p'

#set-options "--z3rlimit 50"
let lemma_find_helper (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, d = sel h (index uf i) in
          reify (find uf p h) h == reify (find uf i h) h)
  = let p, s = sel h (index uf i) in
    if p = i then ()
    else ()
#reset-options

#set-options "--z3rlimit 50"
let lemma_find_opt_helper (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, d = sel h (index uf i) in
          p = i \/
	  (let pp, hp = reify (find_opt uf p h) h in
            let pi, hi = reify (find_opt uf i h) h in
	    pp = pi /\ (hi == upd hp (index uf i) (pp, d))))
  = let p, s = sel h (index uf i) in
    if p = i then ()
    else ()
#reset-options

(* let lemma_0 (uf:uf_forest) (i:id uf) (h:heap{live uf h /\ well_formed uf h}) :GTot unit = *)
(*   let p, s = sel h (index uf i) in *)
(*   if p = i then () *)
(*   else begin *)
(*     let pp, h1 = reify (find_opt uf p h) h in *)
(*     let _, h2 = reify (find_opt uf i h) h in *)
(*     assert (h2 == upd h1 (index uf i) (pp, s)); *)
(*     () *)
(*   end *)

(* let lemma_1 (uf:uf_forest) (i:id uf) (h:heap{live uf h /\ well_formed uf h}) :GTot unit = *)
(*   let p, s = sel h (index uf i) in *)
(*   if p = i then () *)
(*   else begin *)
(*     let pp, h1 = reify (find_opt uf p h) h in *)
(*     let _, h2 = reify (find_opt uf i h) h in *)
(*     assert (forall (a:Type) (r:ref a). addr_of r <> addr_of (index uf i) ==> sel h1 r == sel h2 r); *)
(*     //assert (h2 == upd h1 (index uf i) (pp, s)); *)
(*     () *)
(*   end *)
(*
 * a simple warm up lemma
 * proving that find and find_opt return the same value
 * we don't prove anything about the resultant heaps, yet
 *)
let rec lemma_find_find_opt_same_result (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (requires  True)
         (ensures   (fst (reify (find uf i h) h) = fst (reify (find_opt uf i h) h)))
	 (decreases (length uf - height #n uf i h))
  = let p, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      lemma_find_find_opt_same_result uf p h
    end

(*
 * after find_opt, either parent of a node j remains same, or
 * the parent is j's root in the original heap
 *)
let rec lemma_find_opt_parent_same_as_find_root (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h}) (j:id n)
  :Lemma (requires True)
         (ensures  (let _, h0 = reify (find uf i h) h in
	            let _, h1 = reify (find_opt uf i h) h in

                    let p0 = parent uf j h0 in
		    let p1 = parent uf j h1 in

                    p0 = p1 \/ (p1 = fst (reify (find uf j h0) h0) /\ parent uf p1 h1 = p1)))
	 (decreases (length uf - height #n uf i h))
  = let p, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      lemma_find_opt_parent_same_as_find_root uf p h j;
      ignore (reify (find uf p h) h);
      ignore (reify (find_opt uf p h) h);
      ignore (reify (find uf j h) h);  //AR: in general there is need for these triggers ... need to look into it
      lemma_find_opt_helper uf i h;
      if j <> i then ()
      else begin  //else we invoke the lemma that find and find_opt return same result, for both p and i
        lemma_find_find_opt_same_result uf i h;
    	lemma_find_find_opt_same_result uf p h
      end
    end

(*
 * equivalence of find and find_opt
 * in particular, we prove that find of a node j in h1 (the resultant heap after path compression)
 * is same as find of j in h0
 *)
#set-options "--z3rlimit 50"
let rec lemma_find_find_opt_equivalence (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h}) (j:id n)
  :Lemma (requires True)
         (ensures  (let _, h0 = reify (find uf i h) h in
	            let _, h1 = reify (find_opt uf i h) h in

                    let r0, _ = reify (find uf j h0) h0 in
		    let r1, _ = reify (find uf j h1) h1 in
		    r0 = r1))  //root of a node remains same in h0 and h1, i.e. find_opt does not change the find query
	 (decreases (length uf - height #n uf j h))
  = 
    let _, h0 = reify (find uf i h) h in
    let _, h1 = reify (find_opt uf i h) h in

    lemma_find_opt_parent_same_as_find_root uf i h j;

    let p0, _ = sel h0 (index uf j) in
    let p1, _ = sel h1 (index uf j) in
    lemma_find_helper uf j h0;
    lemma_find_helper uf j h1;

    //lemma_find_opt_parent_same_as_find_root tells us that either p0 = p1,
    //or p1 = root of j in h0
  
    if p0 = p1 then begin
      if j = p0 then ()  //if j = p0 = p1, then find returns j immediately, so we are done
      else begin  //else we invoke I.H. on p0, and then one unrolling of find call on j uses it to give us the proof
        lemma_find_find_opt_equivalence uf i h p0
      end
    end
    else  //p0 <> p1, but p1 = root of j in h0 and p1's parent = p1 in h1, so, root of j in h1 is p1 = root of j in h0
      begin
        assert (p1 = fst (reify (find uf j h0) h0));
	assert (parent uf p1 h1 = p1);
	assert (p1 = fst (reify (find uf p1 h1) h1));
	()
      end
