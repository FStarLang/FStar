module LowStar.Lens.Inclusion

open LowStar.Lens
open FStar.HyperStack.ST

module B = LowStar.Buffer
module DM = FStar.DependentMap
module DGM = FStar.DependentGMap


let ptr_t (#t:eqtype) (f:t -> Type) = DM.t t (fun x -> B.pointer (f x))

let val_t (#t:eqtype) (f:t -> Type) = DGM.t t f

noeq type lens_includes_aux (#t1:eqtype) (#t2:eqtype) 
                            (#f1:t1 -> Type) (#f2:t2 -> Type)
                            (l1:hs_lens (ptr_t f1) (val_t f1))
                            (l2:hs_lens (ptr_t f2) (val_t f2)) =
  {
    dn : t1 -> option t2;
    up : t2 -> t1
  }

let lens_includes (#t1:eqtype) (#t2:eqtype) 
                  (#f1:t1 -> Type) (#f2:t2 -> Type)
                  (l1:hs_lens (ptr_t f1) (val_t f1))
                  (l2:hs_lens (ptr_t f2) (val_t f2)) =
  inc:lens_includes_aux l1 l2 {
    // Key inclusion between the inner and oter lenses (via the up-down conversions on keys)
    (forall k . inc.dn (inc.up k) = Some k) /\
    (forall k . (Some? (inc.dn k)) ==> inc.up (Some?.v (inc.dn k)) = k) /\
    (forall k . f2 k == f1 (inc.up k)) /\
    // Inner and oter lenses have to agree on their views (via the up-down conversions on keys)
    (forall k h . DGM.sel (view l2 h) k == DGM.sel (view l1 h) (inc.up k)) /\
    // Maximally the larger footprint changes between the outer and inner snapshots
    (B.modifies (as_loc l1.footprint) l1.snapshot l2.snapshot) /\
    // The inner invariant is included in the outer one
    (forall h . l1.invariant l1.x h ==> l2.invariant l2.x h) /\
    // Modifying the outer footprint on the outer snapshot should imply modifying the inner footprint on the inner snapshot
    (forall h . B.modifies (as_loc l1.footprint) l1.snapshot h ==> B.modifies (as_loc l2.footprint) l2.snapshot h) /\
    // Domains of inner and outer snapshots are equal
    (FStar.HyperStack.ST.equal_domains l1.snapshot l2.snapshot) /\
    // Relating the invariant on initial and final heaps when running the inner computation    // [DA: doesn't look right, perhaps we need 2-state invariants to properly relate h0 and h1;
    (forall h0 h1 . l1.invariant l1.x h0 /\ B.modifies (as_loc l1.footprint) l1.snapshot h0 /\ //      also, maybe such an implication should already be coming from the def. of a lens?]
                    l2.invariant l2.x h1 /\ B.modifies (as_loc l2.footprint) l2.snapshot h1
                    ==> 
                    l1.invariant l1.x h1 /\ B.modifies (as_loc l1.footprint) l1.snapshot h1)
  }

let pre_t (#t1:eqtype) (#t2:eqtype) 
          (#f1:t1 -> Type) (#f2:t2 -> Type)
          (#l1:hs_lens (ptr_t f1) (val_t f1))
          (#l2:hs_lens (ptr_t f2) (val_t f2))
          (inc:l1 `lens_includes` l2)
          (pre:val_t f2 -> Type) 
          (vals:val_t f1) = 
  pre (DGM.create (fun k -> DGM.sel vals (inc.up k)))

let reveal_pre (#t1:eqtype) (#t2:eqtype) 
               (#f1:t1 -> Type) (#f2:t2 -> Type) 
               (#l1:hs_lens (ptr_t f1) (val_t f1)) 
               (#l2:hs_lens (ptr_t f2) (val_t f2))
               (inc:l1 `lens_includes` l2) 
               (pre:val_t f2 -> Type)
               (vals:val_t f1)
  : Lemma (pre_t inc pre vals 
           <==> 
           pre (DGM.create (fun k -> DGM.sel vals (inc.up k)))) 
  = () 

let post_t (#t1:eqtype) (#t2:eqtype) 
           (#f1:t1 -> Type) (#f2:t2 -> Type)
           (#l1:hs_lens (ptr_t f1) (val_t f1))
           (#l2:hs_lens (ptr_t f2) (val_t f2))
           (inc:l1 `lens_includes` l2)
           (#a:Type)
           (post:val_t f2 -> a -> val_t f2 -> Type) 
           (vals0:val_t f1)
           (x:a)
           (vals1:val_t f1) =
  (post (DGM.create (fun k -> DGM.sel vals0 (inc.up k))) 
        x 
        (DGM.create (fun k -> DGM.sel vals1 (inc.up k))))
  /\
  (forall k . None? (inc.dn k) ==> DGM.sel vals0 k == DGM.sel vals1 k)

let frame (#t1:eqtype) (#t2:eqtype) 
          (#f1:t1 -> Type) (#f2:t2 -> Type)
          (#l1:hs_lens (ptr_t f1) (val_t f1))
          (#l2:hs_lens (ptr_t f2) (val_t f2))
          (inc:l1 `lens_includes` l2)
          (#a:Type)
          (#pre:val_t f2 -> Type)
          (#post:val_t f2 -> a -> val_t f2 -> Type)
          (f:unit -> LensST a l2 pre post) 
  : LensST a l1 (pre_t inc pre) (post_t inc post) = 
  reveal_inv ();
  let h0 = get () in

  assert (inv l1 h0); // l1.invariant l1.x h0 /\ B.modifies (as_loc l1.footprint) l1.snapshot h0 /\ FStar.HyperStack.ST.equal_domains l1.snapshot h0
                      // ==>
  assert (inv l2 h0); // l2.invariant l2.x h0 /\ B.modifies (as_loc l2.footprint) l2.snapshot h0 /\ FStar.HyperStack.ST.equal_domains l2.snapshot h0

  assert (pre_t inc pre (view l1 h0)); //pre (DGM.create (fun k -> DGM.sel (view l1 h0) (inc.up k)))
  reveal_pre inc pre (view l1 h0);
  DGM.equal_intro (DGM.create (fun k -> DGM.sel (view l1 h0) (inc.up k))) (view l2 h0);
  assert (pre (view l2 h0));

  let x = f () in
  let h1 = get () in

  assert (inv l2 h1); // l2.invariant l2.x h1 /\ B.modifies (as_loc l2.footprint) l2.snapshot h1 /\ FStar.HyperStack.ST.equal_domains l2.snapshot h1
  assert (inv l1 h1); // l1.invariant l1.x h1 /\ B.modifies (as_loc l1.footprint) l1.snapshot h1 /\ FStar.HyperStack.ST.equal_domains l1.snapshot h1

  assert (post (view l2 h0) x (view l2 h1));
  DGM.equal_intro (view l2 h1) (DGM.create (fun k -> DGM.sel (view l1 h1) (inc.up k)));
  assert (post (DGM.create (fun k -> DGM.sel (view l1 h0) (inc.up k))) 
               x 
               (DGM.create (fun k -> DGM.sel (view l1 h1) (inc.up k))));

  assume (forall k . None? (inc.dn k) ==> DGM.sel (view l1 h0) k == DGM.sel (view l1 h1) k);

  admit ()

(*

verification condition for frame:

(fun (k:a -> HS.mem -> Type) (h0:HS.mem) ->

  inv l1 h0 /\ 
  
  pre_t inc pre (view l1 h0) /\ 
  
  (forall (x:a) (h1:HS.mem).
  
    inv l1 h1 /\ 

    post_t inc post (view l1 h0) x (view l1 h1) ==> 

    k x h1))

==>

(fun (k:a -> HS.mem -> Type) (h0:HS.mem) ->

  inv l2 h0 /\ 
  
  pre (view l2 h0) /\ 
  
  (forall (x:a) (h1:HS.mem).
  
    inv l2 h1 /\ 

    post (view l2 h0) x (view l2 h1) ==> 

    k x h1))
*)
