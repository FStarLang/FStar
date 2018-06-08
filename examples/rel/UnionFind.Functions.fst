module UnionFind.Functions

open FStar.Seq
open FStar.Ghost
open FStar.OrdSet

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

open UnionFind.Forest

(* helpers for getting the parent, height, and the subtree *)
unfold let parent  (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot (id n)    = Mktuple3?._1 (sel h (index uf i))
unfold let height  (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot nat         = Mktuple3?._2 (sel h (index uf i))
unfold let subtree (#n:nat) (uf:uf_forest n) (i:id n) (h:heap) :GTot subtree_t = reveal (Mktuple3?._3 (sel h (index uf i)))

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
 let rec find (#n:nat) (uf:uf_forest n) (i:id n) (ghost_heap:heap)
  :ST (id n) (requires  (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
             (ensures   (fun h0 r h1 -> h0 == h1 /\ parent uf r h1 = r))
	     (decreases (diff n (subtree #n uf i ghost_heap)))
  = let (p, _, _) = get uf i in
    if p = i then i
    else find uf p ghost_heap

#set-options "--z3rlimit 20"
 let rec find_opt (#n:nat) (uf:uf_forest n) (i:id n) (ghost_heap:heap)
  :ST (id n) (requires (fun h0      -> ghost_heap == h0 /\ live uf h0 /\ well_formed uf h0))
             (ensures  (fun h0 r h1 -> live uf h1 /\ well_formed uf h1 /\ parent uf r h1 = r /\  //these are from find
	                            (r = i \/ strict_subset (subtree uf i h1) (subtree uf r h1)) /\  //we need this because when we write p' as i's parent
				                                                   //we need to ensure wellformedness i.e. subtree of p'
										   //is a strict superset of subtee of i
				     (forall (j:id n).{:pattern (sel h1 (index uf j)) \/ (sel h0 (index uf j))} strict_subset (subtree uf j h0) (subtree uf i h0) ==>
	                                          sel h1 (index uf j) == sel h0 (index uf j))))  //this last clause to say that i remains unchanged in the recursive call, else when we write its subtree to be s, we have trouble proving that p's subtree is a strict superset of s
	      (decreases (diff n (subtree #n uf i ghost_heap)))
  = let (p, d, s) = get uf i in
    if p = i then i
    else
      let h = STATE?.get () in
      let p' = find_opt uf p h in
      set uf i (p', d, s);
      p'
#reset-options

let well_formed_decreases_lemma (#n:nat) (uf:uf_forest n) (i:id n) (h:heap{live uf h /\ well_formed uf h})
  :Lemma (let p, _, _ = sel h (index uf i) in
          p = i \/ diff n (subtree #n uf i h) > diff n (subtree #n uf p h))
  = ()

 let merge (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n)
  : ST unit (requires (fun h0      -> live uf h0 /\ well_formed uf h0))
            (ensures  (fun h0 _ h1 -> live uf h1 /\ well_formed uf h1))
  = let r_1 = find uf i_1 (STATE?.get ()) in
    let r_2 = find uf i_2 (STATE?.get ()) in

    let _, d_1, s_1 = get uf r_1 in
    let _, d_2, s_2 = get uf r_2 in
    if r_1 = r_2 then ()
    else begin
      set uf r_1 (r_2, d_1, s_1);
      //let d_2 = if d_1 >= d_2 then d_1 + 1 else d_2 in
      set uf r_2 (r_2, d_2, elift2 union s_1 s_2);
      assert (strict_subset (reveal s_1) (union (reveal s_1) (reveal s_2)))
    end

 let merge_opt (#n:nat) (uf:uf_forest n) (i_1:id n) (i_2:id n)
  :ST unit (requires (fun h0      -> live uf h0 /\ well_formed uf h0))
           (ensures  (fun h0 _ h1 -> live uf h1 /\ well_formed uf h1))
  = let r_1 = find uf i_1 (STATE?.get ()) in
    let r_2 = find uf i_2 (STATE?.get ()) in

    let _, d_1, s_1 = get uf r_1 in
    let _, d_2, s_2 = get uf r_2 in

    if r_1 = r_2 then ()
    else begin
      if d_1 < d_2 then begin
        set uf r_1 (r_2, d_1, s_1);
        set uf r_2 (r_2, d_2, elift2 union s_1 s_2);
        assert (strict_subset (reveal s_1) (union (reveal s_1) (reveal s_2)))
      end
      else begin
        set uf r_2 (r_1, d_2, s_2);
	let d_1 = if d_1 = d_2 then d_1 + 1 else d_1 in
        set uf r_1 (r_1, d_1, elift2 union s_1 s_2);
        assert (strict_subset (reveal s_1) (union (reveal s_1) (reveal s_2)))
      end
    end
