module Relational.UnionFind

open FStar.Seq
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

(* immediate parent index, height (a.k.a. rank) of the node *)
type elt = nat * nat

(* array representation, ith index is the ith node maintaining its parent and height *)
type uf_forest = seq (ref elt)

(* valid index in the union-find forest *)
type id (uf:uf_forest) = i:nat{i < length uf}

(* liveness and separation condition for the forest *)
let live (uf:uf_forest) (h:heap) :Type0 =
  (forall (i:id uf).{:pattern addr_of (index uf i)} forall (j:id uf).{:pattern addr_of (index uf j)}
               i <> j ==> addr_of (index uf i) <> addr_of (index uf j)) /\  //all the refs in the forest are distinct
  (forall (i:id uf).{:pattern (h `contains_a_well_typed` (index uf i))}
               h `contains_a_well_typed` (index uf i))  //all the refs in the forest are well typed

(* helpers for getting the parent and height *)
unfold let parent (uf:uf_forest) (i:id uf) (h:heap) :GTot nat = fst (sel h (index uf i))
unfold let height (uf:uf_forest) (i:id uf) (h:heap) :GTot nat = snd (sel h (index uf i))

(*
 * well-formed conditions on the forest, essentially the invariants needed for proving the termination of operations
 * TODO: add the pattern, perhaps {:pattern (sel h (index uf i))}?
 *)
let well_formed (uf:uf_forest) (h:heap) =
  forall (i:id uf).
               parent uf i h < length uf /\
               height uf i h < length uf /\
               (parent uf i h = i \/ height uf i h < height uf (parent uf i h) h)

(*
 * the postcondition parent uf r h1 = r is added because of merge, see below in comments
 *)
reifiable let rec find (uf:uf_forest) (i:id uf) (ghost_heap:heap)
  :ST (id uf) (requires  (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
              (ensures   (fun h0 r h1 -> h0 == h1 /\ parent uf r h1 = r))
	      (decreases (length uf - height uf i ghost_heap))
  = let (p, _) = read (index uf i) in
    if p = i then i
    else begin
      assert (forall (i:id uf). height uf i ghost_heap < length uf);  //this is an annoying assert, should go away with better modeling
      find uf p ghost_heap
    end      

reifiable let rec merge (uf:uf_forest) (i_1:id uf) (i_2:id uf)
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

reifiable let rec find_opt (uf:uf_forest) (i:id uf) (ghost_heap:heap)
  :ST (id uf) (requires (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
              (ensures  (fun h0 r h1 -> live uf h1 /\ well_formed uf h1 /\ parent uf r h1 = r /\  //these are from find
	                             (r = i \/ height uf r h1 > height uf i h1) /\  //we need this because when we write p' as i's parent
				                                                   //we need to ensure wellformedness i.e. height of p'
										   //is more than the height of i
				     (forall (j:id uf). height uf j h0 < height uf i h0 ==>
	                                           sel h1 (index uf j) = sel h0 (index uf j))))  //this last clause to say that i remains unchanged in the recursive call, else when we write its height to be d, we have trouble proving that p's height is more than d
	      (decreases (length uf - height uf i ghost_heap))
  = let (p, d) = read (index uf i) in
    if p = i then i
    else
      let h = STATE?.get () in
      let p' = find_opt uf p h in
      write (index uf i) (p', d);
      p'

let rec lemma_0 (uf:uf_forest) (i:id uf) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (requires  True)
         (ensures   (let r0, h0 = reify (find uf i h) h in
                     let r1, h1 = reify (find_opt uf i h) h in
	             r0 = r1))
	 (decreases (length uf - height uf i h))
  = let p, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      assert (forall (i:id uf). height uf i h < length uf);
      lemma_0 uf p h
    end

#set-options "--z3rlimit 50"
let rec lemma_1 (uf:uf_forest) (i:id uf) (h:heap{live uf h /\ well_formed uf h}) (j:id uf)
  :Lemma (requires True)
         (ensures  (let _, h0 = reify (find uf i h) h in
	            let _, h1 = reify (find_opt uf i h) h in

                    let p0, _ = sel h0 (index uf j) in
		    let p1, _ = sel h1 (index uf j) in

                    p0 = p1 \/ (p1 = fst (reify (find uf j h0) h0) /\ parent uf p1 h1 = p1)))
	 (decreases (length uf - height uf i h))
  = let p, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      assert (forall (i:id uf). height uf i h < length uf);
      lemma_1 uf p h j;
      let _, h0 = reify (find uf p h) h in
      let _, h1 = reify (find_opt uf p h) h in
      let p0, _ = sel h0 (index uf j) in
      let p1, _ = sel h1 (index uf j) in
      assert (p0 = p1 \/ (p1 = fst (reify (find uf j h0) h0)));
      lemma_0 uf i h;  //proof takes more time without this, since it has to unfold reify (find uf i h0) when j = i
      lemma_0 uf p h
    end

let rec lemma_2 (uf:uf_forest) (i:id uf) (h:heap{live uf h /\ well_formed uf h}) (j:id uf)
  :Lemma (requires True)
         (ensures  (let _, h0 = reify (find uf i h) h in
	            let _, h1 = reify (find_opt uf i h) h in

                    let p0, _ = reify (find uf j h0) h0 in
		    let p1, _ = reify (find uf j h1) h1 in
		    p0 = p1))
	 (decreases (length uf - height uf j h))
  = lemma_1 uf i h j;
    let _, h0 = reify (find uf i h) h in
    let _, h1 = reify (find_opt uf i h) h in

    assert (h0 == h);

    let p0, _ = sel h0 (index uf j) in
    let p1, _ = sel h1 (index uf j) in

    assert (p0 = p1 \/ (p1 = fst (reify (find uf j h) h) /\ parent uf p1 h1 = p1));
    if p0 = p1 then begin
      assert (forall (i:id uf). height uf i h < length uf);
      assume (height uf p0 h > height uf j h);
      lemma_2 uf i h p0;
      () //this actually goes through, takes time
    end
    else begin
      assert (p1 = fst (reify (find uf j h) h));
      if (p1 = j) then ()
      else
        assert (fst (reify (find uf j h1) h1) = fst (reify (find uf p1 h1) h1));
	assert (parent uf p1 h1 = p1);
	assert (fst (reify (find uf p1 h1) h1) = p1);
	()
    end
      
	(* assert (forall (i:id uf). let j = parent uf i h in *)
	(*                      j <> r_1 ==> addr_of (index uf j) <> addr_of ref_1); *)
	(* assert (forall (i:id uf). ~ (parent uf i h = r_1 \/ parent uf i h = r_2) ==>  *)
	(*                      (addr_of (index uf i) <> addr_of ref_1 /\ *)
	(* 		      addr_of (index uf i) <> addr_of ref_2 /\ *)
	(* 		      addr_of (index uf (parent uf i h)) <> addr_of ref_1 /\ *)
	(* 		      addr_of (index uf (parent uf i h)) <> addr_of ref_2)); *)
        //assert (forall (i:id uf). ~ (parent uf i h = r_2 \/ parent uf i h = r_1 \/ parent uf i h = i) ==> height uf i h < height uf (parent uf i h) h);
	//assert (well_formed uf h);


    //let h0 = STATE?.get () in
    //assert (well_formed uf h0);
    //assert (forall (i:id uf). ~ (parent uf i h0 = r_2 \/ parent uf i h0 = r_1 \/ parent uf i h0 = i) ==> height uf i h0 < height uf (parent uf i h0) h0);
    //assert (forall (i:id uf). ~ (parent uf i h0 = r_2 \/ parent uf i h0 = r_1) ==> height uf i h0 < height uf (parent uf i h0) h0);
    (* assert (forall (i:id uf). (parent uf i h0 = r_2 /\ addr_of (index uf i) <> addr_of ref_2) ==> height uf i h0 < height uf (parent uf i h0) h0); *)
    (* admit () *)

      
      
      (* let h0' = STATE?.get () in *)
      (* let _ = write ref_1 (p_2, d_2 + 1) in () in *)
      (* let h1 = STATE?.get () in *)
      (* assert (forall (i:id uf). parent uf i h1 < length uf); *)
      (* assert (live uf h1); *)
      (* assert (forall (i:id uf). i <> r_1 ==> addr_of (index uf i) <> addr_of (index uf r_1)); *)
      (* assert (forall (a:Type) (r:ref a). addr_of r <> addr_of ref_1 ==> sel h1 r == sel h0' r); *)
      (* assert (forall (i:id uf). (i <> r_1) ==> addr_of (index uf i) <> addr_of ref_1); *)
      (* assert (forall (i:id uf). (i <> r_1 ==> sel h1 (index uf i) = sel h0' (index uf i))); *)
      (* assert (forall (i:id uf). (i <>r_1 ==> (parent uf i h1 = i \/ depth uf i h1 > depth uf (parent uf i h1) h1))); *)
      (* admit () *)
  
  
  (* let r_1 = index uf i_1 in *)
  (*   let r_2 = index uf i_2 in *)
  
  (*   let p_1, d_1 = read r_1 in *)
  (*   let p_2, d_2 = read r_2 in *)
  
  (*   if p_1 = p_2 then () *)
  (*   else *)
  (*     write r_1 (p_2, d_2 +      *)

        (* let h = STATE?.get () in *)
	(* assert (forall (i:id uf). parent uf i h < length uf); *)
	(* assert (forall (i:id uf). height uf i h < length uf); *)
	(* assert (height uf r_1 h < height uf (parent uf r_1 h) h); *)
	(* assert (parent uf r_2 h = r_2); *)
	
	(* assert (forall (i:id uf). (addr_of (index uf i) <> addr_of ref_1 /\ *)
	(*                       addr_of (index uf i) <> addr_of ref_2) ==> sel h (index uf i) = sel h0 (index uf i)); *)
        (* assert (forall (i:id uf). parent uf i h = r_1 ==> height uf i h < height uf (parent uf i h) h); *)
        (* assert (forall (i:id uf). (parent uf i h = r_2 ==> (i = r_2 \/ height uf i h < height uf (parent uf i h) h))); *)
	(* //assert (live uf h); *)
	(* assert (index uf r_1 == ref_1); *)
