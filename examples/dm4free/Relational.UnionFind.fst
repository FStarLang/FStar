module Relational.UnionFind

open FStar.Seq
open FStar.OrdSet

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

open Relational.UnionFind.Forest
open Relational.UnionFind.Functions

let lemma_find_helper (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, _, _ = sel h (index uf i) in
          reify (find uf p h) h == reify (find uf i h) h)
  = ()

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
