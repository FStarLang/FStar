module PulseCore.Heap2
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open FStar.PCM
module Frac = PulseCore.FractionalPermission
module PP = PulseCore.Preorder
module H = PulseCore.Heap

noeq
type heap : Type u#(a + 1) = {
  concrete : H.heap u#a; 
  ghost    : erased (H.heap u#a);
}

let empty_heap = { concrete = H.empty_heap; ghost = H.empty_heap }

let core_ref = H.core_ref
let core_ref_null = H.core_ref_null
let core_ref_is_null = H.core_ref_is_null

let disjoint (h1:heap) (h2:heap) =
  H.disjoint h1.concrete h2.concrete /\ H.disjoint h1.ghost h2.ghost

let disjoint_sym h0 h1 = ()
let join h0 h1 = {
  concrete = H.join h0.concrete h1.concrete;
  ghost = H.join h0.ghost h1.ghost;
}
let join_commutative' (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 == join m1 m0)
    [SMTPat (join m0 m1)]
  = H.join_commutative m0.concrete m1.concrete;
    H.join_commutative m0.ghost m1.ghost

let join_commutative h0 h1 =
  H.join_commutative h0.concrete h1.concrete;
  H.join_commutative h0.ghost h1.ghost
let disjoint_join h0 h1 h2 =
  H.disjoint_join h0.concrete h1.concrete h2.concrete;
  H.disjoint_join h0.ghost h1.ghost h2.ghost
let join_associative h0 h1 h2 =
  H.join_associative h0.concrete h1.concrete h2.concrete;
  H.join_associative h0.ghost h1.ghost h2.ghost

let join_associative2 (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2)
    (ensures
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) /\
      join m0 (join m1 m2) == join (join m0 m1) m2)
    [SMTPat (join (join m0 m1) m2)]
  = disjoint_join m2 m0 m1;
    join_commutative m2 m1;
    join_associative m0 m1 m2

let slprop = p:(heap ^-> prop) { heap_prop_is_affine p }
let interp p m = p m
let as_slprop f = F.on _ f
let slprop_extensionality p q = FStar.PredicateExtensionality.predicateExtensionality _ p q
let emp = as_slprop (fun _ -> True)
assume
val of_slprop (f:H.slprop) : H.a_heap_prop
assume
val slprop_inj (f:H.slprop) : Lemma (H.as_slprop (of_slprop f) == f)
                                    [SMTPat (of_slprop f)]

let lift (p:H.slprop) : slprop =
  as_slprop (fun h -> of_slprop p h.concrete)
let pts_to #a #pcm (r:ref a pcm) (v:a) = lift (H.pts_to #a #pcm r v)
let star p1 p2 =
  as_slprop (fun (h: heap) ->
    exists (h1 h2 : heap).
        h1 `disjoint` h2 /\
        h == join h1 h2 /\
        interp p1 h1 /\
        interp p2 h2)
let h_exists #a f = as_slprop (fun h -> exists (x:a). interp (f x) h)
let affine_star p1 p2 h = ()
let equiv_symmetric p1 p2 = ()
let equiv_extensional_on_star p1 p2 p3 = ()
let emp_unit p = admit()
let intro_emp h = ()
let h_exists_cong #a p q = ()
let intro_h_exists x p h = ()
let elim_h_exists #a p h = ()
let interp_depends_only_on hp = ()
let h_join_empty (h:H.heap)
  : Lemma (H.disjoint h H.empty_heap /\
           H.join h H.empty_heap == h)
           [SMTPatOr
              [[SMTPat (H.disjoint h H.empty_heap)];
               [SMTPat (H.join h H.empty_heap)]]]
  = admit()
let pts_to_compatible #a #pcm (x:ref a pcm) (v0 v1:a) h = 
  H.pts_to_compatible #a #pcm x v0 v1 h.concrete;
  introduce interp (pts_to x v0 `star` pts_to x v1) h ==>
            composable pcm v0 v1 /\
            interp (pts_to x (op pcm v0 v1)) h
  with _ . (
    eliminate exists h0 h1.
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp (pts_to x v0) h0 /\
      interp (pts_to x v1) h1
    returns
      composable pcm v0 v1 /\
      interp (pts_to x (op pcm v0 v1)) h
    with _ . (
      H.intro_star (H.pts_to #a #pcm x v0) (H.pts_to #a #pcm x v1) h0.concrete h1.concrete;
      H.pts_to_compatible #a #pcm x v0 v1 h0.concrete
    )
  );
  introduce (composable pcm v0 v1 /\
             interp (pts_to x (op pcm v0 v1)) h) ==>
            interp (pts_to x v0 `star` pts_to x v1) h
  with _ . (
    assert (H.interp (H.pts_to #a #pcm x (op pcm v0 v1)) h.concrete);
    H.pts_to_compatible #a #pcm x v0 v1 h.concrete;
    assert (H.interp (H.pts_to #a #pcm x v0 `H.star` H.pts_to #a #pcm x v1) h.concrete);
    H.elim_star (H.pts_to #a #pcm x v0) (H.pts_to #a #pcm x v1) h.concrete;
    eliminate exists c0 c1.
      H.disjoint c0 c1 /\ 
      h.concrete == H.join c0 c1 /\
      H.interp (H.pts_to #a #pcm x v0) c0 /\
      H.interp (H.pts_to #a #pcm x v1) c1
    returns interp (pts_to x v0 `star` pts_to x v1) h
    with _ . (
      let h0 = { h with concrete = c0 } in
      let h1 = { concrete = c1; ghost = H.empty_heap } in
      assert (disjoint h0 h1);
      assert (interp (lift (H.pts_to #a #pcm x v0)) h0);
      assert (interp (lift (H.pts_to #a #pcm x v1)) h1);
      assert (h == join h0 h1)
    )
  )

let pts_to_join #a #pcm (r:ref a pcm) (v1 v2:a) h =
  H.pts_to_join #a #pcm r v1 v2 h.concrete

let pts_to_join' #a #pcm r v1 v2 h =
  H.pts_to_join' #a #pcm r v1 v2 h.concrete

let pts_to_compatible_equiv #a #pcm r v0 v1 =
  H.pts_to_compatible_equiv #a #pcm r v0 v1;
  assert (H.equiv (H.pts_to #a #pcm r v0 `H.star` H.pts_to #a #pcm r v1)
                  (H.pts_to #a #pcm r (op pcm v0 v1)));
  introduce forall h.
      interp (pts_to #a #pcm r v0 `star` pts_to #a #pcm r v1) h <==>
      interp (pts_to #a #pcm r (op pcm v0 v1)) h
  with (
    introduce
      interp (pts_to #a #pcm r v0 `star` pts_to #a #pcm r v1) h ==>
      interp (pts_to #a #pcm r (op pcm v0 v1)) h
    with _ . (
      eliminate exists h0 h1.
        disjoint h0 h1 /\
        h == join h0 h1 /\
        interp (pts_to #a #pcm r v0) h0 /\
        interp (pts_to #a #pcm r v1) h1
      returns _
      with _ . (
        H.intro_star (H.pts_to #a #pcm r v0) (H.pts_to #a #pcm r v1) h0.concrete h1.concrete
      )
    );
    introduce
      interp (pts_to #a #pcm r (op pcm v0 v1)) h ==>
      interp (pts_to #a #pcm r v0 `star` pts_to #a #pcm r v1) h
    with _ . (
      H.elim_star (H.pts_to #a #pcm r v0) (H.pts_to #a #pcm r v1) h.concrete;
      eliminate exists c0 c1.
        H.disjoint c0 c1 /\ 
        h.concrete == H.join c0 c1 /\
        H.interp (H.pts_to #a #pcm r v0) c0 /\
        H.interp (H.pts_to #a #pcm r v1) c1
      returns _
      with _ . (
        let h0 = { h with concrete = c0 } in
        let h1 = { concrete = c1; ghost = H.empty_heap } in
        assert (disjoint h0 h1)
      )
    )
  )

let pts_to_not_null #a #pcm x v m = H.pts_to_not_null #a #pcm x v m.concrete

let intro_star p q h hq = ()
let elim_star p q h = ()
let star_commutative p1 p2 = ()
let star_associative p1 p2 p3 = ()
let star_congruence p1 p2 q1 q2 = ()

let pure p = as_slprop (fun _ -> p)
let pure_equiv p q = FStar.PropositionalExtensionality.apply p q
let pure_interp q h = ()
let pure_star_interp p q h = ()

let stronger_star p q r = ()
let weaken p q r h = ()

let full_heap_pred h = H.full_heap_pred h.concrete /\ H.full_heap_pred h.ghost
let heap_evolves (h0 h1:full_heap) =
  H.heap_evolves h0.concrete h1.concrete /\
  H.heap_evolves h0.ghost h1.ghost
let free_above_addr h a = H.free_above_addr h.concrete a
let weaken_free_above h a b = H.weaken_free_above h.concrete a b

(** [sel_v] is a ghost read of the value contained in a heap reference *)
let sel_v' (#a:Type u#h) (#pcm:pcm a) (r:ref a pcm) (v:erased a) (m:full_hheap (pts_to r v))
  : v':a{ compatible pcm v v' /\
          pcm.refine v' /\
          interp (ptr r) m /\
          True
          }
  = let v = H.sel_v #a #pcm r v m.concrete in
    // assert (H.interp (H.ptr #a #pcm r) m.concrete);
    // assert (exists v. H.interp (H.pts_to #a #pcm r v) m.concrete);
    // assert (exists v. interp (pts_to r v) m);
    // assert (interp (ptr r) m);
    v

let lower_ptr #a #pcm (r:ref a pcm) (m:full_hheap (ptr r))
: Lemma (H.interp (H.ptr #a #pcm r) m.concrete)
= eliminate exists v. H.interp (H.pts_to #a #pcm r v) m.concrete
  returns H.interp (H.ptr #a #pcm r) m.concrete
  with _ . ( H.intro_h_exists v (H.pts_to #a #pcm r) m.concrete )

let raise_ptr #a #pcm (r:ref a pcm) (m:full_heap)
: Lemma 
  (requires
    H.interp (H.ptr #a #pcm r) m.concrete)
  (ensures
    interp (ptr r) m)
= H.elim_h_exists (H.pts_to #a #pcm r) m.concrete;
  eliminate exists v. H.interp (H.pts_to #a #pcm r v) m.concrete
  returns interp (ptr #a #pcm r) m
  with _ . ()

(** [sel] is a ghost read of the value contained in a heap reference *)
let sel (#a:Type u#h) (#pcm:pcm a) (r:ref a pcm) (m:full_hheap (ptr r)) : a =
 lower_ptr r m;
 H.sel #a #pcm r m.concrete
 
let sel_v (#a:Type u#h) (#pcm:pcm a) (r:ref a pcm) (v:erased a) (m:full_hheap (pts_to r v))
  : v':a{ compatible pcm v v' /\
          pcm.refine v' /\
          interp (ptr r) m /\
          v' == sel r m
          }
  = H.sel_v #a #pcm r v m.concrete

let sel_lemma #a #pcm r m = lower_ptr r m; H.sel_lemma #a #pcm r m.concrete
let elim_heap_evolves (h0 h1:full_heap)
: Lemma 
  (requires heap_evolves h0 h1)
  (ensures H.heap_evolves h0.concrete h1.concrete /\
           H.heap_evolves h0.ghost h1.ghost)
= assert (heap_evolves h0 h1 ==> 
            (H.heap_evolves h0.concrete h1.concrete /\ H.heap_evolves h0.ghost h1.ghost))
      by (FStar.Tactics.norm [delta_only [`%heap_evolves]])


let witnessed_ref_stability #a #pcm r fact = 
  H.witnessed_ref_stability #a #pcm r fact;
  assert (FStar.Preorder.stable (H.witnessed_ref #a #pcm r fact) H.heap_evolves);
  introduce forall h0 h1. 
    (witnessed_ref r fact h0 /\
     heap_evolves h0 h1) ==>
    witnessed_ref r fact h1
  with (
    introduce _ ==> _
    with _ . (
      assert (interp (ptr r) h0 /\ fact (sel r h0));
      lower_ptr r h0;
      assert (H.interp (H.ptr #a #pcm r) h0.concrete);
      assert (heap_evolves h0 h1);
      elim_heap_evolves h0 h1;
      assert (H.heap_evolves h0.concrete h1.concrete);
      assert (H.witnessed_ref #a #pcm r fact h1.concrete);
      raise_ptr r h1;
      assert (sel r h1 == H.sel #a #pcm r h1.concrete)
    )
  )

let lift_heap_pre_action
      (#fp:H.slprop) (#a:Type) (#fp':a -> H.slprop)
      (act:H.pre_action fp a fp')
: pre_action (lift fp) a (fun x -> lift (fp' x))
= fun (h0:full_hheap (lift fp)) ->
    let (| x, c |) = act h0.concrete in
    let h1 : full_hheap (lift (fp' x)) = { h0 with concrete=c } in
    (| x, h1 |)

#restart-solver

let lift_action
      (#fp:H.slprop) (#a:Type) (#fp':a -> H.slprop)
      (act:H.action fp a fp')
: action (lift fp) a (fun x -> lift (fp' x))
= let p = lift_heap_pre_action act in
  introduce forall frame (h0:full_hheap (lift fp `star` frame)).
    let (| x, h1 |) = p h0 in
    interp (lift (fp' x) `star` frame) h1 /\
    action_related_heaps frame h0 h1
  with (
    assert (interp (lift fp `star` frame) h0);
    let (| x, h1 |) = p h0 in
    eliminate exists h0' h1'.
      disjoint h0' h1' /\
      h0 == join h0' h1' /\
      interp (lift fp) h0' /\
      interp frame h1'
    returns 
      interp (lift (fp' x) `star` frame) h1 /\
      action_related_heaps frame h0 h1
    with _ . (
      let hframe : H.heap -> prop = (fun h -> interp frame { concrete = h; ghost = h1'.ghost }) in
      introduce forall c0 c1.
        (hframe c0 /\ H.disjoint c0 c1)
         ==> 
        hframe (H.join c0 c1)
      with (
        introduce _ ==> _
        with _ . (
          let h0g = {concrete=c0; ghost=h1'.ghost} in
          assert (interp frame h0g);
          assert (H.disjoint c0 c1);
          assert (heap_prop_is_affine frame);
          let h1g = { concrete = c1; ghost = H.empty_heap } in
          assert (disjoint h0g h1g);
          assert (interp frame (join h0g h1g));
          assert (hframe (H.join c0 c1))
        )
      );
      assert (H.heap_prop_is_affine hframe);
      let hframe : H.slprop = H.as_slprop hframe in
      assert (H.interp fp h0'.concrete);
      assert (H.interp hframe h1'.concrete);
      H.intro_star fp hframe h0'.concrete h1'.concrete;
      let h00 : H.full_hheap (fp `H.star` hframe) = h0.concrete in
      let h11 : H.full_hheap (fp' x `H.star` hframe) = dsnd (act h00) in
      assert (h1 == { h0 with concrete = h11 });
      // assr
      // assert (H.interp (fp' x `H.star` hframe) h1'.concrete);
      admit()
    );
    admit()
     
    // let (| x, h1 |) = p h0 in
    // assert (h1.concrete == dsnd <| act h0.concrete);
    // assert (H.heap_evolves h0.concrete h1.concrete);
    // admit();
    // assert (action_related_heaps frame h0 h1);
    // admit()
  );
  p
 