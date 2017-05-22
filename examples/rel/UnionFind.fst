module UnionFind

open FStar.Seq
open FStar.Ghost
open FStar.OrdSet

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

open UnionFind.Forest
open UnionFind.Functions

let lemma_find_helper (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, _, _ = sel h (index uf i) in
          reify (find uf p h) h == reify (find uf i h) h)
  = ()

let rec lemma_find_height_independence (#n:nat) (uf:uf_forest n) (i:id n)
  (h_1:heap{live uf h_1 /\ well_formed uf h_1})
  (h_2:heap{live uf h_2 /\ well_formed uf h_2})
  :Lemma (requires (forall (j:id n).
                      parent uf j h_1 = parent uf j h_2 /\
                      subtree uf j h_1 == subtree uf j h_2))
	 (ensures  (let r_1, h'_1 = reify (find uf i h_1) h_1 in
	            let r_2, h'_2 = reify (find uf i h_2) h_2 in
		    r_1 = r_2 /\ h'_1 == h_1 /\ h'_2 == h_2))
	 (decreases (diff n (subtree #n uf i h_1)))
  = let p_1 = parent uf i h_1 in
    if p_1 = i then ()
    else begin    
      well_formed_decreases_lemma uf i h_1;
      lemma_find_height_independence uf p_1 h_1 h_2
    end

(*
 * lemma to condense find_opt behavior
 *)
#set-options "--z3rlimit 10"
let lemma_find_opt_helper (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, d, s = sel h (index uf i) in
          p = i \/
	  (let pp, hp = reify (find_opt uf p h) h in
           let pi, hi = reify (find_opt uf i h) h in
	   pp = pi /\ (hi == upd hp (index uf i) (pp, d, s))))
  = let p, s, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      ignore (reify (find_opt uf p h) h);
      ignore (reify (find_opt uf i h) h);
      ()
    end
#reset-options

(*
 * a simple warm up lemma
 * proving that find and find_opt return the same value
 * we don't prove anything about the resultant heaps, yet
 *)
let rec lemma_find_find_opt_same_result (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (requires  True)
         (ensures   (fst (reify (find uf i h) h) = fst (reify (find_opt uf i h) h)))
	 (decreases (diff n (subtree #n uf i h)))
  = let p, _, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      well_formed_decreases_lemma uf i h;
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
	 (decreases (diff n (subtree #n uf i h)))
  = let p, _, _ = sel h (index uf i) in
    if p = i then ()
    else begin
      well_formed_decreases_lemma uf i h;
      lemma_find_opt_parent_same_as_find_root uf p h j;
      ignore (reify (find uf p h) h);
      ignore (reify (find_opt uf p h) h);
      ignore (reify (find uf j h) h);
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
#set-options "--z3rlimit 10"
let rec lemma_find_find_opt_equivalence (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h}) (j:id n)
  :Lemma (requires True)
         (ensures  (let _, h0 = reify (find uf i h) h in
	            let _, h1 = reify (find_opt uf i h) h in

                    let r0, _ = reify (find uf j h0) h0 in
		    let r1, _ = reify (find uf j h1) h1 in
		    r0 = r1))  //root of a node remains same in h0 and h1, i.e. find_opt does not change the find query
	 (decreases (diff n (subtree #n uf j h)))
  = 
    let _, h0 = reify (find uf i h) h in
    let _, h1 = reify (find_opt uf i h) h in

    lemma_find_opt_parent_same_as_find_root uf i h j;

    let p0, _, _ = sel h0 (index uf j) in
    let p1, _, _ = sel h1 (index uf j) in
    lemma_find_helper uf j h0;
    lemma_find_helper uf j h1;

    //lemma_find_opt_parent_same_as_find_root tells us that either p0 = p1,
    //or p1 = root of j in h0
    if p0 = p1 then begin
      if j = p0 then ()  //if j = p0 = p1, then find returns j immediately, so we are done
      else begin  //else we invoke I.H. on p0, and then one unrolling of find call on j uses it to give us the proof
	well_formed_decreases_lemma uf j h;
        lemma_find_find_opt_equivalence uf i h p0
      end
    end
    else () //p0 <> p1, but p1 = root of j in h0 and p1's parent = p1 in h1, so, root of j in h1 is p1 = root of j in h0
#reset-options

(* condensing the behavior of merge and merge_opt *)
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 40"
let lemma_merge_helper (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (requires True)
         (ensures  (let r_1, _ = reify (find uf i_1 h) h in
	            let r_2, _ = reify (find uf i_2 h) h in
		    let _, d_1, s_1 = sel h (index uf r_1) in
		    let _, d_2, s_2 = sel h (index uf r_2) in
		    let _, h1 = reify (merge uf i_1 i_2) h in
		    r_1 <> r_2 ==>
		    (sel h1 (index uf r_1) == (r_2, d_1, s_1)                   /\
		     (//let d_2 = if d_1 >= d_2 then d_1 + 1 else d_2 in
		      sel h1 (index uf r_2) == (r_2, d_2, elift2 union s_1 s_2)) /\
		     (forall (j:id n). (j <> r_1 /\ j <> r_2) ==> sel h (index uf j) == sel h1 (index uf j)))))
  = let r_1, _ = reify (find uf i_1 h) h in
    let r_2, _ = reify (find uf i_2 h) h in
    ()

let lemma_merge_opt_helper (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (requires True)
         (ensures  (let r_1, _ = reify (find uf i_1 h) h in
	            let r_2, _ = reify (find uf i_2 h) h in
		    let _, d_1, s_1 = sel h (index uf r_1) in
		    let _, d_2, s_2 = sel h (index uf r_2) in
		    let _, h1 = reify (merge_opt uf i_1 i_2) h in
		    (r_1 <> r_2 /\ d_1 >= d_2) ==>
		    (sel h1 (index uf r_2) == (r_1, d_2, s_2)                   /\
		     (let d_1 = if d_1 = d_2 then d_1 + 1 else d_1 in
		      sel h1 (index uf r_1) == (r_1, d_1, elift2 union s_1 s_2)) /\
		     (forall (j:id n). (j <> r_1 /\ j <> r_2) ==> sel h (index uf j) == sel h1 (index uf j)))))
  = ()
#reset-options

#set-options "--z3rlimit 40"
let lemma_merge_height_independence (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n)
  (h_1:heap{live uf h_1 /\ well_formed uf h_1})
  (h_2:heap{live uf h_2 /\ well_formed uf h_2})
  :Lemma (requires (forall (j:id n). parent uf j h_1 = parent uf j h_2 /\
                                subtree uf j h_1 == subtree uf j h_2))
	 (ensures  (let _, h'_1 = reify (merge uf i_1 i_2) h_1 in
	            let _, h'_2 = reify (merge uf i_1 i_2) h_2 in
		    (forall (j:id n). parent uf j h'_1 = parent uf j h'_2    /\
		                 subtree uf j h'_1 == subtree uf j h'_2 /\
				 height uf j h'_1 = height uf j h_1     /\
				 height uf j h'_2 = height uf j h_2)))
  = let r_1, _ = reify (find uf i_1 h_1) h_1 in
    let r_2, _ = reify (find uf i_2 h_1) h_1 in
    lemma_find_height_independence uf i_1 h_1 h_2;
    lemma_find_height_independence uf i_2 h_1 h_2;
    if r_1 = r_2 then ()
    else begin
      lemma_merge_helper uf i_1 i_2 h_1;
      lemma_merge_helper uf i_1 i_2 h_2;
      ()
    end
#reset-options

(*
 * proving that for a node whose root is not any of the components being merged, the root remains unchanged,
 * for both merge and merge_opt
 * we consider only the scenario where merge and merge_opt differ
 * i.e. r_1 <> r_2 /\ height uf r_1 h >= height uf r_2 h
 * in the other case, merge and merge_opt behave same, so the proof for their equivalence goes easily
 *)
#set-options "--z3rlimit 20"
let rec lemma_merge_merge_opt_equivalence_helper_diff (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n) (h:heap{live uf h /\ well_formed uf h})
  (j:id n)
  :Lemma (requires (let r_1, _ = reify (find uf i_1 h) h in
	            let r_2, _ = reify (find uf i_2 h) h in

                    let p, _ = reify (find uf j h) h in

                    r_1 <> r_2  /\ height uf r_1 h >= height uf r_2 h /\
		    p <> r_1 /\ p <> r_2))  //p is neither r_1 nor r_2
         (ensures  (let _, h1 = reify (merge uf i_1 i_2) h in
	            let _, h2 = reify (merge_opt uf i_1 i_2) h in

                    fst (reify (find uf j h1) h1) = fst (reify (find uf j h) h) /\
                    fst (reify (find uf j h2) h2) = fst (reify (find uf j h) h)))  //find of j remains same in as h in h1 and h2
	 (decreases %[diff n (subtree #n uf j h)])
  = let r_1, _ = reify (find uf i_1 h) h in
    let r_2, _ = reify (find uf i_2 h) h in
    
    let _, h1 = reify (merge uf i_1 i_2) h in
    let _, h2 = reify (merge_opt uf i_1 i_2) h in

    //recall the behavior of merge and merge_opt
    lemma_merge_helper uf i_1 i_2 h;
    lemma_merge_opt_helper uf i_1 i_2 h;

    let p = parent uf j h in
    if j = p then ()
    else begin
      //I.H.
      well_formed_decreases_lemma uf j h;
      lemma_merge_merge_opt_equivalence_helper_diff uf i_1 i_2 h p;
      //recall the behavior of find
      lemma_find_helper uf j h1;
      lemma_find_helper uf j h2;
      ()
    end

(*
 * proving that for a node whose root is one of the components being merged, it is r_1 in one case, r_2 in the other
 * we consider only the scenario where merge and merge_opt differ
 * i.e. r_1 <> r_2 /\ height uf r_1 h >= height uf r_2 h
 * in the other case, merge and merge_opt behave same, so the proof for their equivalence goes easily
 *)
#set-options "--z3rlimit 20"
let rec lemma_merge_merge_opt_equivalence_helper_same (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n) (h:heap{live uf h /\ well_formed uf h})
  (j_1:id n)
  :Lemma (requires (let r_1, _ = reify (find uf i_1 h) h in
	            let r_2, _ = reify (find uf i_2 h) h in

                    let p_1, _ = reify (find uf j_1 h) h in

                    r_1 <> r_2 /\ height uf r_1 h >= height uf r_2 h /\  //consider only the case where the behavior of merge and merge_opt differs
		    (p_1 = r_1 \/ p_1 = r_2)))  //j_1 is in one of the two componenets being merged
         (ensures  (let r_1, _ = reify (find uf i_1 h) h in
	            let r_2, _ = reify (find uf i_2 h) h in
	 
	            let _, h1 = reify (merge uf i_1 i_2) h in
	            let _, h2 = reify (merge_opt uf i_1 i_2) h in

                    fst (reify (find uf j_1 h1) h1) = r_2 /\  //for merge the root is r_1
                    fst (reify (find uf j_1 h2) h2) = r_1))  //for merge_opt the root is r_2
	 (decreases %[diff n (subtree #n uf j_1 h)])
  = let r_1, _ = reify (find uf i_1 h) h in
    let r_2, _ = reify (find uf i_2 h) h in
    
    let _, h1 = reify (merge uf i_1 i_2) h in
    let _, h2 = reify (merge_opt uf i_1 i_2) h in

    //recall the behavior of merge and merge_opt
    lemma_merge_helper uf i_1 i_2 h;
    lemma_merge_opt_helper uf i_1 i_2 h;
  
    let p_1 = parent uf j_1 h in
    if j_1 = p_1 then ()
    else begin  //if j_1 <> p_1, use I.H. on p_1
      well_formed_decreases_lemma uf j_1 h;
      lemma_merge_merge_opt_equivalence_helper_same uf i_1 i_2 h p_1;
      lemma_find_helper uf j_1 h1;
      lemma_find_helper uf j_1 h2;
      ()
    end

#set-options "--z3rlimit 20"
let lemma_merge_merge_opt_equivalence (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n) (h:heap{live uf h /\ well_formed uf h})
  (j_1:id n) (j_2:id n)
  :Lemma (requires True)
         (ensures  (let _, h1 = reify (merge uf i_1 i_2) h in
	            let _, h2 = reify (merge_opt uf i_1 i_2) h in
		    
                    (fst (reify (find uf j_1 h1) h1) = fst (reify (find uf j_2 h1) h1)) <==>
                    (fst (reify (find uf j_1 h2) h2) = fst (reify (find uf j_2 h2) h2))))
  = let r_1, _ = reify (find uf i_1 h) h in
    let r_2, _ = reify (find uf i_2 h) h in

    let _, d_1, s_1 = sel h (index uf r_1) in
    let _, d_2, s_2 = sel h (index uf r_2) in

    if r_1 = r_2 then ()
    else if j_1 = j_2 then ()
    else begin
      if d_1 < d_2 then ()
      else begin
        let p_1, _ = reify (find uf j_1 h) h in
	let p_2, _ = reify (find uf j_2 h) h in

        //now there are 4 scenarios, depending on if p_1 is in one of the trees being merged
	//and if p_2 is in one of the trees being merged
	//doing a 4-way case analysis
        if (p_1 = r_1 || p_1 = r_2) then
	  if (p_2 = r_1 || p_2 = r_2) then begin
	    lemma_merge_merge_opt_equivalence_helper_same #n uf i_1 i_2 h j_1;
	    lemma_merge_merge_opt_equivalence_helper_same #n uf i_1 i_2 h j_2
	  end
	  else begin
	    lemma_merge_merge_opt_equivalence_helper_same #n uf i_1 i_2 h j_1;
	    lemma_merge_merge_opt_equivalence_helper_diff #n uf i_1 i_2 h j_2
	  end
	else
	  if (p_2 = r_1 || p_2 = r_2) then begin
	    lemma_merge_merge_opt_equivalence_helper_diff #n uf i_1 i_2 h j_1;
	    lemma_merge_merge_opt_equivalence_helper_same #n uf i_1 i_2 h j_2
	  end
	  else begin
	    lemma_merge_merge_opt_equivalence_helper_diff #n uf i_1 i_2 h j_1;
	    lemma_merge_merge_opt_equivalence_helper_diff #n uf i_1 i_2 h j_2
	  end
	end
    end
