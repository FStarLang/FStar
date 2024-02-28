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
let concrete h = h.concrete
let ghost h = h.ghost
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
let lift (p:H.slprop) : slprop =
  as_slprop (fun h -> H.of_slprop p h.concrete)
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
let h_join_empty (h:H.heap)
  : Lemma (H.disjoint h H.empty_heap /\
           H.join h H.empty_heap == h)
           [SMTPatOr
              [[SMTPat (H.disjoint h H.empty_heap)];
               [SMTPat (H.join h H.empty_heap)]]]
  = H.join_empty h
let emp_unit p = 
  assert (forall h. disjoint h empty_heap /\ join h empty_heap == h)
let intro_emp h = ()
let h_exists_cong #a p q = ()
let intro_h_exists x p h = ()
let elim_h_exists #a p h = ()
let interp_depends_only_on hp = ()

let lift_star (p q:H.slprop)
: Lemma (lift (p `H.star` q) == (lift p `star` lift q))
        [SMTPat (lift (p `H.star` q))]
= introduce forall m.
    interp (lift (p `H.star` q)) m <==>
    interp (lift p `star` lift q) m
  with (
    introduce 
      interp (lift p `star` lift q) m ==>
      interp (lift (p `H.star` q)) m
    with _ . ( 
      eliminate exists h0 h1.
        disjoint h0 h1 /\
        m == join h0 h1 /\
        interp (lift p) h0 /\
        interp (lift q) h1
      returns interp (lift (p `H.star` q)) m
      with _ . (
        H.intro_star p q h0.concrete h1.concrete
      )
    );
    introduce 
      interp (lift (p `H.star` q)) m ==>
      interp (lift p `star` lift q) m
    with _ . ( 
      H.elim_star p q m.concrete;
      eliminate exists c0 c1.
        H.disjoint c0 c1 /\
        m.concrete == H.join c0 c1 /\
        H.interp p c0 /\
        H.interp q c1
      returns interp (lift p `star` lift q) m
      with _ . (
        let h0 = { concrete = c0; ghost = m.ghost } in
        let h1 = { concrete = c1; ghost = H.empty_heap } in
        assert (disjoint h0 h1)
      )
    )
  );
  slprop_extensionality (lift (p `H.star` q)) (lift p `star` lift q)
let lift_emp : squash (lift H.emp == emp) = 
  FStar.Classical.forall_intro H.intro_emp;
  slprop_extensionality (lift H.emp) emp

let pts_to_compatible #a #pcm (x:ref a pcm) (v0 v1:a) h = 
  H.pts_to_compatible #a #pcm x v0 v1 h.concrete;
  lift_star (H.pts_to #a #pcm x v0) (H.pts_to #a #pcm x v1)

let pts_to_join #a #pcm (r:ref a pcm) (v1 v2:a) h =
  H.pts_to_join #a #pcm r v1 v2 h.concrete

let pts_to_join' #a #pcm r v1 v2 h =
  H.pts_to_join' #a #pcm r v1 v2 h.concrete

let pts_to_compatible_equiv #a #pcm r v0 v1 =
  H.pts_to_compatible_equiv #a #pcm r v0 v1;
  lift_star (H.pts_to #a #pcm r v0) (H.pts_to #a #pcm r v1)

let pts_to_not_null #a #pcm x v m = H.pts_to_not_null #a #pcm x v m.concrete

let intro_star p q h hq = ()
let elim_star p q h = ()
let star_commutative p1 p2 = ()
#push-options "--fuel 0 --ifuel 4 --z3rlimit_factor 4 --z3cliopt smt.qi.eager_threshold=1000000"
let star_associative p1 p2 p3 = ()
#pop-options
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
let heap_evolves_iff (h0 h1:full_heap)
: Lemma 
  (ensures
     heap_evolves h0 h1 <==> (
      H.heap_evolves h0.concrete h1.concrete /\
      H.heap_evolves h0.ghost h1.ghost))
= assert (heap_evolves h0 h1 <==> 
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
      heap_evolves_iff h0 h1;
      assert (H.heap_evolves h0.concrete h1.concrete);
      assert (H.witnessed_ref #a #pcm r fact h1.concrete);
      raise_ptr r h1;
      assert (sel r h1 == H.sel #a #pcm r h1.concrete)
    )
  )

let lift_pred (pre:H.full_heap -> prop)
  : full_heap -> prop
  = fun h -> pre h.concrete

let lift_heap_pre_action
      (#pre #post:_) (#fp:H.slprop) (#a:Type) (#fp':a -> H.slprop)
      (act:H.pre_action #pre #post fp a fp')
: pre_action #(lift_pred pre) #(lift_pred post) (lift fp) a (fun x -> lift (fp' x))
= fun (h0:full_hheap (lift fp) { lift_pred pre h0 }) ->
    let (| x, c |) = act h0.concrete in
    let h1 : full_hheap (lift (fp' x)) = { h0 with concrete=c } in
    (| x, h1 |)

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
let lift_immut (m:bool) = if m then IMMUTABLE else MUTABLE
let lift_action
      (#immut #allocs #pre #post:_)
      (#fp:H.slprop) (#a:Type) (#fp':a -> H.slprop)
      (act:H.action #immut #allocs #pre #post fp a fp')
: action #(lift_immut immut) #allocs #(lift_pred pre) #(lift_pred post)
        (lift fp) a (fun x -> lift (fp' x))
= let p = lift_heap_pre_action act in
  let mut = lift_immut immut in
  introduce forall frame (h0:full_hheap (lift fp `star` frame) { lift_pred pre h0 }).
    let (| x, h1 |) = p h0 in
    interp (lift (fp' x) `star` frame) h1 /\
    action_related_heaps #mut #allocs h0 h1
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
      action_related_heaps #mut #allocs h0 h1
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
      H.elim_star (fp' x) hframe h11;
      eliminate exists c0 c1.
        H.disjoint c0 c1 /\
        h11 == H.join c0 c1 /\
        H.interp (fp' x) c0 /\
        H.interp hframe c1
      returns interp (lift (fp' x) `star` frame) h1
      with _ . ( 
        let h10 = { concrete = c0; ghost = h0'.ghost } in
        let h11 = { concrete = c1; ghost = h1'.ghost } in
        assert (interp (lift (fp' x)) h10);
        assert (interp frame h11);
        assert (disjoint h10 h11)
      );
      heap_evolves_iff h0 h1;
      assert (action_related_heaps #mut #allocs h0 h1)
    )
  );
  p

let sel_action #a #pcm r v0 = lift_action (H.sel_action #a #pcm r v0)
let select_refine #a #p r x f = lift_action (H.select_refine #a #p r x f)
let upd_gen_action #a #p r x y f = lift_action (H.upd_gen_action #a #p r x y f)
let upd_action #a #p r x y = lift_action (H.upd_action #a #p r x y)
let free_action #a #p r v0 = lift_action (H.free_action #a #p r v0)
let split_action #a #p r v0 v1 = lift_action (H.split_action #a #p r v0 v1)
let gather_action #a #p r v0 v1 = lift_action (H.gather_action #a #p r v0 v1)
let pts_to_not_null_action #a #p r v = lift_action (H.pts_to_not_null_action #a #p r v)
let extend #a #pcm x addr = lift_action (H.extend #a #pcm x addr)

let refined_pre_action (#mut:mutability) (#allocates:bool)
                       (#[T.exact (`trivial_pre)]pre:full_heap ->prop)
                       (#[T.exact (`trivial_pre)]post:full_heap -> prop)
                       (fp0:slprop) (a:Type) (fp1:a -> slprop) =
  m0:full_hheap fp0 ->
  Pure (x:a &
        full_hheap (fp1 x))
       (requires pre m0)
       (ensures fun  (| x, m1 |) ->
         post m1 /\
         (forall frame. frame_related_heaps m0 m1 fp0 (fp1 x) frame mut allocates))

#restart-solver
let refined_pre_action_as_action #immut #allocs #pre #post (#fp0:slprop) (#a:Type) (#fp1:a -> slprop)
                                 ($f:refined_pre_action #immut #allocs #pre #post fp0 a fp1)
  : action #immut #allocs #pre #post fp0 a fp1
  = let g : pre_action fp0 a fp1 = fun m -> f m in
    g

let frame (#a:Type)
          (#immut #allocates #hpre #hpost:_)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action pre a post)
  = let g 
      : refined_pre_action #immut #allocates #hpre #hpost 
          (pre `star` frame) a (fun x -> post x `star` frame)
        = fun h0 ->
              assert (interp (pre `star` frame) h0);
              affine_star pre frame h0;
              let (| x, h1 |) = f h0 in
              assert (interp (post x) h1);
              assert (interp (post x `star` frame) h1);
              assert (forall frame'. frame_related_heaps h0 h1 pre (post x) frame' immut allocates);
              introduce forall frame'.
                    (interp ((pre `star` frame) `star` frame') h0 ==>
                     interp ((post x `star` frame) `star` frame') h1)
              with (
                star_associative pre frame frame';
                star_associative (post x) frame frame'
              );
              (| x, h1 |)
    in
    refined_pre_action_as_action g


let change_slprop (p q:slprop)
                  (proof: (h:heap -> Lemma (requires interp p h) (ensures interp q h)))
  : action #IMMUTABLE #no_allocs p unit (fun _ -> q)
  = let g
      : refined_pre_action p unit (fun _ -> q)
      = fun h ->
          FStar.Classical.forall_intro (FStar.Classical.move_requires proof);
          (| (), h |)
    in
    refined_pre_action_as_action g


let witness_h_exists #a p =
  fun frame h0 ->
  let w = FStar.IndefiniteDescription.indefinite_description_tot
    a
    (fun x -> interp (p x `star` frame) h0) in
  (| w, h0 |)

let intro_exists #a p x =
  fun frame h0 ->
    intro_h_exists (reveal x) p h0;
    (| (), h0 |)

module U = FStar.Universe    

let lift_h_exists (#a:_) (p:a -> slprop)
  : action (h_exists p) unit
           (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))
  = let g : refined_pre_action #IMMUTABLE #no_allocs (h_exists p) unit (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))
          = fun h ->
              introduce forall x h.
                  interp (p x) h ==>
                  interp (h_exists (U.lift_dom p)) h
              with (
                introduce _ ==> _
                with _ . (
                  assert (interp (U.lift_dom p (U.raise_val x)) h)
                )
              );
              (| (), h |)
    in
    refined_pre_action_as_action g

let elim_pure (p:prop)
  : action (pure p) (u:unit{p}) (fun _ -> emp)
  = let f
      : refined_pre_action (pure p) (_:unit{p}) (fun _ -> emp)
      = fun h -> (| (), h |)
    in
    refined_pre_action_as_action f

let intro_pure (p:prop) (_:squash p)
: action emp unit (fun _ -> pure p)
= let f
    : refined_pre_action emp unit (fun _ -> pure p)
    = fun h -> (| (), h |)
  in
  refined_pre_action_as_action f

let pts_to_evolve (#a:Type u#a) (#pcm:_) (r:ref a pcm) (x y : a) (h:heap)
  : Lemma (requires (interp (pts_to r x) h /\ compatible pcm y x))
          (ensures  (interp (pts_to r y) h))
  = H.pts_to_evolve #a #pcm r x y h.concrete

let drop p
= let f
    : refined_pre_action p unit (fun _ -> emp)
    = fun h -> (| (), h |)
  in
  refined_pre_action_as_action f

let is_frame_preserving_only_ghost 
    (#a: Type u#a)
    (#pre #post:_)
    (#fp: slprop u#b)
    (#fp': a -> slprop u#b)
    (f:pre_action #pre #post fp a fp')
    (h:full_hheap fp { pre h })
: Lemma 
  (requires is_frame_preserving ONLY_GHOST false f)
  (ensures (dsnd (f h)).concrete == h.concrete)
= emp_unit fp;
  let h : full_hheap (fp `star` emp) = h in
  eliminate forall frame (h0:full_hheap (fp `star` frame) { pre h0 }). (
      affine_star fp frame h0 ;
      (dsnd (f h0)).concrete == h0.concrete)
  with emp h

    

type non_informative (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

let lift_erased
          (#a:Type)
          (#ni_a:non_informative a)
           #hpre #hpost
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:erased (action #ONLY_GHOST #hpre #hpost pre a post))
: action #ONLY_GHOST #hpre #hpost pre a post
= let g : refined_pre_action #ONLY_GHOST #hpre #hpost pre a post =
    fun h ->
      let gg : erased (a & H.heap) =
        let ff : action #ONLY_GHOST #hpre #hpost pre a post = reveal f in
        let (| x, hh' |) = ff h in
        is_frame_preserving_only_ghost ff h;
        Ghost.hide (x, Ghost.reveal hh'.ghost)
      in
      let x = ni_a (Ghost.hide (fst gg)) in
      let gg = Ghost.hide (snd gg) in
      (| x, { h with ghost = gg } |)
  in
  refined_pre_action_as_action g