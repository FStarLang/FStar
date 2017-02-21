module Relational.UnionFind

open FStar.Seq
open FStar.OrdSet

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

type subtree_t = ordset nat (fun x y -> x <= y)

(***** some boring set lemmas *****)
assume val minus: subtree_t -> subtree_t -> Tot subtree_t
assume val strict_subset: subtree_t -> subtree_t -> Tot bool
assume val set_n (n:nat): subtree_t

let lemma_strict_subset_size (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires (strict_subset s1 s2))
         (ensures  (subset s1 s2 /\ size s1 < size s2))
   [SMTPat (strict_subset s1 s2)]
  = admit ()

let lemma_minus_mem (s1:subtree_t) (s2:subtree_t) (x:nat)
  :Lemma (requires True) (ensures (mem x (minus s1 s2) = (mem x s1 && not (mem x s2))))
   [SMTPat (mem x (minus s1 s2))]
  = admit ()

let lemma_strict_subset_minus_size (s:subtree_t) (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires (strict_subset s1 s2 /\ subset s1 s /\ subset s2 s))
         (ensures  (size (minus s s2) < size (minus s s1)))
   [SMTPat (strict_subset s1 s2); SMTPat (subset s1 s); SMTPat (subset s2 s)]
  = admit ()

let lemma_disjoint_union_subset (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires (~ (s1 == empty) /\ ~ (s2 == empty) /\ intersect s1 s2 == empty))
         (ensures  (strict_subset s1 (union s1 s2) /\ strict_subset s2 (union s1 s2)))
   [SMTPatOr [[SMTPat (strict_subset s1 (union s1 s2))]; [SMTPat (strict_subset s2 (union s1 s2))]]]
  = admit ()

let lemma_subset_union (s1:subtree_t) (s2:subtree_t) (n:nat)
  :Lemma (requires (subset s1 (set_n n) /\ subset s2 (set_n n)))
         (ensures  (subset (union s1 s2) (set_n n)))
   [SMTPat (subset (union s1 s2) (set_n n))]
  = ()

let lemma_strict_subset_transitive (s1:subtree_t) (s2:subtree_t) (s3:subtree_t)
  :Lemma (requires (strict_subset s1 s2 /\ strict_subset s2 s3))
         (ensures  (strict_subset s1 s3))
   [SMTPat (strict_subset s1 s2); SMTPat (strict_subset s2 s3)]
  = admit ()

let lemma_intersect_transitive (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires True) (ensures (intersect s1 s2 == intersect s2 s1))
   [SMTPatOr [[SMTPat (intersect s1 s2)]; [SMTPat (intersect s2 s1)]]]
  = admit ()

let lemma_intersect_union_empty (s1:subtree_t) (s2:subtree_t) (s3:subtree_t)
  :Lemma (requires (intersect s1 s3 == empty /\ intersect s2 s3 == empty))
         (ensures  (intersect (union s1 s2) s3 == empty))
   [SMTPat (intersect (union s1 s2) s3)]
  = admit ()
(***** end boring set lemmas *****)

type id (n:nat) = i:nat{i < n}

(*
 * each node maintains its parent id, height, and subtree nodes (including itself)
 * the subtree set is used as the decreasing metric
 *)
type elt (n:nat) = id n * id n * subtree_t

type uf_forest (n:nat) = s:seq (ref (elt n)){length s = n}

(* liveness and separation condition for the unionfind forest *)
let live (#n:nat) (uf:uf_forest n) (h:heap) :Type0 =
  (forall (i:id n).{:pattern addr_of (index uf i)} forall (j:id n).{:pattern addr_of (index uf j)}
               i <> j ==> addr_of (index uf i) <> addr_of (index uf j)) /\  //all the refs in the forest are distinct
  (forall (i:id n).{:pattern (h `contains_a_well_typed` (index uf i))}
               h `contains_a_well_typed` (index uf i))  //all the refs in the forest are well typed

(* helpers for getting the parent, height, and the subtree *)
unfold let parent  (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot (id n)    = Mktuple3?._1 (sel h (index uf i))
unfold let height  (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot (id n)    = Mktuple3?._2 (sel h (index uf i))
unfold let subtree (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot subtree_t = Mktuple3?._3 (sel h (index uf i))

(*
 * well-formed conditions on the forest, essentially the invariants needed for proving the termination of operations
 * my suspicion is that these patterns are not too helpful
 *)
let well_formed (#n:nat) (uf:uf_forest n) (h:heap) =
  forall (i:id n). {:pattern (sel h (index uf i))}
             (let p = parent uf i h in
	      let s = subtree uf i h in
	      mem i s /\  //at least i itself is in the subtree
	      subset s (set_n n) /\  //s is a subset of set_n
	      (forall (j:id n). {:pattern (sel h (index uf j))}  //different roots have disjoint subtrees
	                  (i <> j /\ i = p /\ j = parent uf j h) ==> intersect s (subtree uf j h) == empty) /\
	      (p = i \/ strict_subset s (subtree uf p h)))  //either i is its own parent or subtree of i is a strict subset of subtree of p

(* the metric that decreases in the recursive calls *)
let diff (n:nat) (s:subtree_t) :Tot nat = size (minus (set_n n) s)

(*
 * the postcondition parent uf r h1 = r is added because of merge, see below in comments
 *)
reifiable let rec find (#n:nat) (uf:uf_forest n) (i:id n) (ghost_heap:heap)
  :ST (id n) (requires  (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
             (ensures   (fun h0 r h1 -> h0 == h1 /\ parent uf r h1 = r))
	     (decreases (diff n (subtree #n uf i ghost_heap)))
  = let (p, _, _) = read (index uf i) in
    if p = i then i
    else find uf p ghost_heap

#set-options "--z3rlimit 10"
let lemma_find_helper (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, _, _ = sel h (index uf i) in
          reify (find uf p h) h == reify (find uf i h) h)
  = ()
#reset-options

#set-options "--z3rlimit 30"
reifiable let rec find_opt (#n:nat) (uf:uf_forest n) (i:id n) (ghost_heap:heap)
  :ST (id n) (requires (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
             (ensures  (fun h0 r h1 -> live uf h1 /\ well_formed uf h1 /\ parent uf r h1 = r /\  //these are from find
	                            (r = i \/ strict_subset (subtree uf i h1) (subtree uf r h1)) /\  //we need this because when we write p' as i's parent
				                                                   //we need to ensure wellformedness i.e. subtree of p'
										   //is a strict superset of subtee of i
				     (forall (j:id n).{:pattern (sel h1 (index uf j))} strict_subset (subtree uf j h0) (subtree uf i h0) ==>
	                                          sel h1 (index uf j) = sel h0 (index uf j))))  //this last clause to say that i remains unchanged in the recursive call, else when we write its subtree to be s, we have trouble proving that p's subtree is a strict superset of s
	      (decreases (diff n (subtree #n uf i ghost_heap)))
  = let (p, d, s) = read (index uf i) in
    if p = i then i
    else
      let h = STATE?.get () in
      let p' = find_opt uf p h in
      write (index uf i) (p', d, s);
      p'
#reset-options

(*
 * lemma to condense find_opt behavior
 *)
#set-options "--z3rlimit 50"
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
#set-options "--z3rlimit 100"
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
    assert (reify (find uf j h0) h0 == reify (find uf p0 h0) h0);
    assert (reify (find uf j h1) h1 == reify (find uf p1 h1) h1);

    //lemma_find_opt_parent_same_as_find_root tells us that either p0 = p1,
    //or p1 = root of j in h0
    assert (p0 = p1 \/ (p1 = fst (reify (find uf j h0) h0) /\ parent uf p1 h1 = p1));
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
	assert (fst (reify (find uf j h1) h1) = fst (reify (find uf p1 h1) h1));
	()
      end
#reset-options

reifiable let rec merge (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n)
  : ST unit (requires (fun h0      -> live uf h0 /\ well_formed uf h0))
            (ensures  (fun h0 _ h1 -> live uf h1 /\ well_formed uf h1))
  = let h0 = STATE?.get () in

    let r_1 = find uf i_1 (STATE?.get ()) in
    let r_2 = find uf i_2 (STATE?.get ()) in

    let ref_1 = index uf r_1 in
    let ref_2 = index uf r_2 in

    let _, d_1, s_1 = !ref_1 in
    let _, d_2, s_2 = !ref_2 in

    if r_1 = r_2 then ()
    else begin
      write ref_1 (r_2, d_1, s_1);
      write ref_2 (r_2, d_2, union s_1 s_2);
      assert (strict_subset s_1 (union s_1 s_2))
    end
