module Steel.Reference

open Steel.Actions
open Steel.SteelAtomic.Basics
module Sem = Steel.Semantics.Hoare.MST

#push-options "--fuel 0 --ifuel 1"
let alloc (#a:Type) (x:a)
  : SteelT (ref a) emp (fun r -> pts_to r full x)
  = Steel?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = alloc_ref x trivial_preorder in
      let (| x, m1 |) = act m0 in
      act_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let read_core (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  : SteelAtomic a uses false (ref_perm r p) (fun x -> pts_to r p x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = get_ref uses r p in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)


let read_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:erased a) (r:ref a)
  : SteelAtomic a uses false (pts_to r p v) (fun x -> pts_to r p x)
  = change_hprop (pts_to r p v) (ref_perm r p) (fun m -> intro_exists v (pts_to_ref r p) m);
    read_core r

let read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)
  = lift_atomic_to_steelT (fun _ -> read_atomic r)

let read_refine_core_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelAtomic a uses false
    (h_exists (fun (v:a) -> pts_to_ref r p v `star` q v))
    (fun x -> pts_to_ref r p x `star` q x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = get_ref_refine uses r p q in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let read_refine_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelAtomic a uses false
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun x -> pts_to r p x `star` q x)
  = change_hprop
      (h_exists (fun (v:a) -> pts_to r p v `star` q v))
      (h_exists (fun (v:a) -> pts_to_ref r p v `star` q v))
      (fun m -> h_exists_extensionality
        (fun (v:a) -> pts_to r p v `star` q v)
        (fun (v:a) -> pts_to_ref r p v `star` q v)
      );
    let x = read_refine_core_atomic q r in
    change_hprop (pts_to_ref r p x `star` q x) (pts_to r p x `star` q x) (fun m -> ());
    return_atomic x

let read_refine (#a:Type) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = lift_atomic_to_steelT (fun _ -> read_refine_atomic q r)

let write_atomic (#a:Type) (#uses:Set.set lock_addr) (#v:erased a) (r:ref a) (x:a)
  : SteelAtomic unit uses false (pts_to r full v) (fun _ -> pts_to r full x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = set_ref uses r v x in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full v) (fun _ -> pts_to r full x)
  = lift_atomic_to_steelT (fun _ -> write_atomic r x)

let free_core (#a:Type) (r:ref a)
  : SteelT unit (ref_perm r full) (fun _ -> emp)
  = Steel?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = free_ref r in
      let (| x, m1 |) = act m0 in
      act_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full v) (fun _ -> emp)
  = lift_atomic_to_steelT (fun _ -> change_hprop (pts_to r full v) (ref_perm r full) (fun m -> intro_exists v (pts_to_ref r full) m));
    free_core r

let share_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:erased a) (r:ref a)
  : SteelAtomic unit
    uses
    true
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = change_hprop
      (pts_to r p v)
      (pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
      (fun m -> share_pts_to_ref r p v m)

let share (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = lift_atomic_to_steelT (fun _ -> share_atomic r)

let gather_atomic
  (#a:Type) (#uses:Set.set lock_addr)
  (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelAtomic unit
    uses
    true
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
  = change_hprop
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (pts_to r (sum_perm p0 p1) v0)
      (fun m -> gather_pts_to_ref r p0 p1 v0 v1 m)

let gather (#a:Type) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
  = lift_atomic_to_steelT (fun _ -> gather_atomic r)

let ghost_read (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      // TODO: Needs to expose such an action. The ref should probably be to Ghost.erased a
      admit())

let ghost_read_refine (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      // TODO: Needs to expose such an action. The ref should probably be to Ghost.erased a
      admit())

let cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_perm v)
    (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = cas uses r v v_old v_new in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let alloc_monotonic_ref = admit()
let read_monotonic_ref = admit()
let write_monotonic_ref = admit()

let pure (p:prop) : hprop =
 refine emp (fun _ -> p)

let witnessed #t #p r fact =
  RMST.witnessed mem mem_evolves (fun m ->
    (interp (ref_or_dead r) m /\ fact (sel_ref_or_dead r m))
  )

#restart-solver

let ac_reasoning_for_witness_atomic (p q: hprop) (f: prop) : Lemma
  (requires f)
  (ensures (p `equiv` (p `star` pure f)))
  =
  calc (equiv) {
    p;
    (equiv) {emp_unit p}
    (p `star` emp);
    (equiv) {star_commutative p emp}
    (emp `star` p);
    (equiv) {
      let aux (h: mem) : Lemma (
        (interp (emp `star` p) h /\ f) <==>
        (interp (refine (emp `star` p) (fun _ -> f)) h)
      ) =
        refine_equiv (emp `star` p) (fun _ -> f) h
      in
      Classical.forall_intro aux
    }
    (refine (emp `star` p) (fun _ -> f));
    (equiv) { refine_star emp p (fun _ -> f)}
    (refine emp (fun _ -> f) `star` p);
    (equiv) { () }
    (pure f `star` p);
    (equiv) { star_commutative (pure f) p }
    (p `star` pure f);
  }


let ac_reasoning_for_frame_on_noop
  (p q r s: hprop)
  (m :mem)
  : Lemma
    (requires ((p `equiv` q) /\
      interp ((p `star` r) `star` s) m
    ))
    (ensures (interp ((q `star` r) `star` s)) m)
  =
  star_associative p r s;
  equiv_extensional_on_star p q (r `star` s);
  assert(interp (q `star` (r `star` s)) m);
  star_associative q r s

#push-options "--fuel 2 --ifuel 1"
let preserves_frame_on_noop
  (uses:Set.set lock_addr)
  (#st: Sem.st{st == state_uses uses})
  (pre post: st.Sem.hprop)
  (m: st.Sem.mem)
  : Lemma
    (requires (forall (m: st.Sem.mem). st.Sem.interp pre m <==> st.Sem.interp post m))
    (ensures (Sem.preserves_frame pre post m m))
  =
   let aux (frame:st.Sem.hprop) : Lemma (
    st.Sem.interp ((pre `st.Sem.star` frame) `st.Sem.star` (st.Sem.locks_invariant m)) m ==>
    (st.Sem.interp ((post `st.Sem.star` frame) `st.Sem.star` (st.Sem.locks_invariant m)) m /\
     (forall (f_frame:Sem.fp_prop frame). f_frame (st.Sem.core m) == f_frame (st.Sem.core m))))
   =
     let aux (_ :squash (
       st.Sem.interp ((pre `st.Sem.star` frame) `st.Sem.star` (st.Sem.locks_invariant m)) m
     )) : Lemma (
       (st.Sem.interp ((post `st.Sem.star` frame) `st.Sem.star` (st.Sem.locks_invariant m)) m /\
       (forall (f_frame:Sem.fp_prop frame). f_frame (st.Sem.core m) == f_frame (st.Sem.core m)))
     ) =
       ac_reasoning_for_frame_on_noop pre post frame (st.Sem.locks_invariant m) m
     in
     Classical.impl_intro aux
   in
   Classical.forall_intro aux
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let witness_atomic
  (#a:Type)
  (#uses:Set.set lock_addr)
  (#q:perm)
  (#p:Preorder.preorder a)
  (r:reference a p)
  (fact:stable_property p)
  (v:(Ghost.erased a))
  (_:squash (fact v))
  : SteelAtomic unit uses true
    (pts_to_ref r q v)
    (fun _ -> pts_to_ref r q v `star` pure (witnessed r fact))
  =
  SteelAtomic?.reflect (fun _ ->
   let m0 = mst_get () in
   intro_exists v (pts_to_ref r q) m0;
   sel_ref_lemma r q m0;
   pts_to_ref_injective r q v (sel_ref r m0) m0;
   let fact_mem : RMST.s_predicate mem = (fun m ->
    interp (ref_or_dead r) m /\ fact (sel_ref_or_dead r m)
   ) in
   let aux (m0 m1: mem) : Lemma ((fact_mem m0 /\ mem_evolves m0 m1) ==> fact_mem m1) =
     let aux (_ :squash (fact_mem m0 /\ mem_evolves m0 m1)) : Lemma (fact_mem m1) =
       reference_preorder_respected r m0 m1
     in
     Classical.impl_intro aux
   in
   Classical.forall_intro_2 aux;
   assert(RMST.stable mem mem_evolves fact_mem);
   sel_ref_or_dead_lemma r m0;
   RMST.witness mem mem_evolves fact_mem;
   let m1 = mst_get () in
   assert(m0 == m1);
   ac_reasoning_for_witness_atomic
     (pts_to_ref r q v)
     (locks_invariant uses m1)
     (witnessed r fact);
   equiv_extensional_on_star
     (pts_to_ref r q v)
     ((pts_to_ref r q v) `star` pure (witnessed r fact))
     (locks_invariant uses m1);
   let aux (m: mem) : Lemma(
     interp (pts_to_ref r q v) m <==> interp (pts_to_ref r q v `star` pure (witnessed r fact)) m
   ) =
     let aux (_ : squash (interp (pts_to_ref r q v) m)) : Lemma (
       interp (pts_to_ref r q v `star` pure (witnessed r fact)) m
     ) =
       ac_reasoning_for_witness_atomic (pts_to_ref r q v) emp (witnessed r fact)
     in
     Classical.impl_intro aux;
     let aux (_ : squash (interp (pts_to_ref r q v `star` pure (witnessed r fact)) m)) : Lemma (
       interp (pts_to_ref r q v) m
     ) =
       affine_star (pts_to_ref r q v) (pure (witnessed r fact)) m
     in
     Classical.impl_intro aux
   in
   Classical.forall_intro aux;
   preserves_frame_on_noop
     uses
     #(state_uses uses)
     (pts_to_ref r q v)
     (pts_to_ref r q v `star` pure (witnessed r fact))
     m0
  )
#pop-options

let witness (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:reference a p)
            (fact:stable_property p)
            (v:(Ghost.erased a))
            (pf:squash (fact v))
  : SteelT unit (pts_to_ref r q v)
                (fun _ -> pts_to_ref r q v `star` pure (witnessed r fact))
  =
  lift_atomic_to_steelT (fun _ -> witness_atomic r fact v pf)

let ac_reasoning_for_recall_atomic (p: hprop) (f: prop) (m: mem) : Lemma
  (requires (interp (p `star` pure f)) m)
  (ensures (f))
  =
  affine_star p (pure f) m;
  refine_equiv emp (fun _ -> f) m

let mst_admit (#a:Type) ()
: Mst a (fun _ -> True) (fun _ _ _ -> False)
= RMST.rmst_admit ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let recall_atomic
  (#a:Type)
  (#uses:Set.set lock_addr)
  (#q:perm)
  (#p:Preorder.preorder a)
  (#fact:property a)
  (r:reference a p)
  (v:(Ghost.erased a))
  : SteelAtomic unit uses true
    (pts_to_ref r q v `star` pure (witnessed r fact))
    (fun _ -> pts_to_ref r q v `star` pure (fact v))
  = SteelAtomic?.reflect (fun _ ->
   let m0 = mst_get () in
   intro_exists v (pts_to_ref r q) m0;
   sel_ref_lemma r q m0;
   pts_to_ref_injective r q v (sel_ref r m0) m0;
   ac_reasoning_for_recall_atomic (pts_to_ref r q v) (witnessed r fact) m0;
   let fact_mem : RMST.s_predicate mem = (fun m ->
    interp (ref_or_dead r) m /\ fact (sel_ref_or_dead r m)
   ) in
   RMST.recall mem mem_evolves fact_mem;
   let m1 = mst_get () in
   assert(m0 == m1);
   sel_ref_or_dead_lemma r m1;
   assert(Ghost.reveal v == sel_ref r m1);
   assert(Ghost.reveal v == sel_ref_or_dead r m1);
   assert(fact (Ghost.reveal v));
   let aux (m: mem) : Lemma(
     interp (pts_to_ref r q v `star` pure (witnessed r fact)) m <==>
     interp (pts_to_ref r q v `star` pure (fact v)) m
   ) =
     let aux (_ : squash (interp (pts_to_ref r q v `star` pure (fact v)) m)) : Lemma (
       interp (pts_to_ref r q v `star` pure (witnessed r fact)) m
     ) =
       affine_star (pts_to_ref r q v) (pure (fact v)) m1;
       ac_reasoning_for_witness_atomic (pts_to_ref r q v) emp (witnessed r fact)
     in
     Classical.impl_intro aux;
     let aux (_ : squash (interp (pts_to_ref r q v `star` pure (witnessed r fact)) m)) : Lemma (
       interp (pts_to_ref r q v `star` pure (fact v)) m
     ) =
       affine_star (pts_to_ref r q v) (pure (witnessed r fact)) m;
       ac_reasoning_for_witness_atomic (pts_to_ref r q v) emp (fact v)
     in
     Classical.impl_intro aux
   in
   Classical.forall_intro aux;
   preserves_frame_on_noop
     uses
     #(state_uses uses)
     (pts_to_ref r q v `star` pure (witnessed r fact))
     (pts_to_ref r q v `star` pure (fact v))
     m0;
   assert (interp (pts_to_ref r q v `star` pure (fact v)) m1);  //from aux
   assume (interp ((pts_to_ref r q v `star` pure (fact v)) `star` (locks_invariant uses m1)) m1)
 )
#pop-options


let recall (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
           (r:reference a p) (v:(Ghost.erased a))
  : SteelT unit (pts_to_ref r q v `star` pure (witnessed r fact))
                (fun _ -> pts_to_ref r q v `star` pure (fact v))

  =
  lift_atomic_to_steelT (fun _ -> recall_atomic r v)
