module PulseCore.TwoLevelHeap
open FStar.Ghost
open FStar.PCM
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
(**** The base : partial heaps *)

(**
  Abstract type of heaps. Can conceptually be thought of as a map from addresses to
  contents of memory cells.
*)
let small_heap = H2.heap u#a

noeq
type heap  : Type u#(a + 2) = {
  small : H2.heap u#a;
  big   : H2.heap u#(a + 1)
}

noeq
type core_heap : Type u#(a + 2) = {
  core_small : H.heap u#a;
  core_big   : H.heap u#(a + 1);
}

let concrete (h:heap) : core_heap = {
  core_small = H2.concrete h.small;
  core_big = H2.concrete h.big
}

let ghost (h:heap) : erased core_heap = {
  core_small = H2.ghost h.small;
  core_big = H2.ghost h.big
}

let upd_ghost_heap
      (h0:heap)
      (h1:erased heap { concrete h0 == concrete h1 })
: h2:heap { h2 == reveal h1 }
= {
    small = H2.upd_ghost_heap h0.small (h1.small);
    big = H2.upd_ghost_heap h0.big (h1.big)
  }

let empty_heap = {
  small = H2.empty_heap;
  big = H2.empty_heap
}

let core_ref = H2.core_ref
let core_ref_null = H2.core_ref_null
let core_ref_is_null r = H2.core_ref_is_null r

let disjoint h0 h1 = H2.disjoint h0.small h1.small /\ H2.disjoint h0.big h1.big


let disjoint_sym h0 h1 = ()
let join h0 h1 = {
  small = H2.join h0.small h1.small;
  big = H2.join h0.big h1.big;
}
let join_commutative' (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 == join m1 m0)
    [SMTPat (join m0 m1)]
  = H2.join_commutative m0.small m1.small;
    H2.join_commutative m0.big m1.big

let join_commutative h0 h1 =
  H2.join_commutative h0.small h1.small;
  H2.join_commutative h0.big h1.big
let disjoint_join h0 h1 h2 =
  H2.disjoint_join h0.small h1.small h2.small;
  H2.disjoint_join h0.big h1.big h2.big
let join_associative h0 h1 h2 =
  H2.join_associative h0.small h1.small h2.small;
  H2.join_associative h0.big h1.big h2.big

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

let h2_join_empty (h:H2.heap)
  : Lemma (H2.disjoint h H2.empty_heap /\
           H2.join h H2.empty_heap == h)
           [SMTPatOr
              [[SMTPat (H2.disjoint h H2.empty_heap)];
               [SMTPat (H2.join h H2.empty_heap)]]]
  = H2.join_empty h
let join_empty h = ()
let slprop = p:(heap u#a ^-> prop) { heap_prop_is_affine p }
let interp p m = p m
let as_slprop f = F.on _ f
let interp_depends_only_on hp = ()
let slprop_extensionality p q = FStar.PredicateExtensionality.predicateExtensionality _ p q

let small_slprop = H2.slprop u#a
let down_p (p:slprop u#a)
: small_heap u#a -> prop
= fun h -> p { small = h; big = H2.empty_heap }
let down_p_affine (p:slprop) : Lemma (H2.heap_prop_is_affine (down_p p)) = 
  introduce forall (h1 h2:small_heap).
          down_p p h1 /\ H2.disjoint h1 h2 ==> down_p p (H2.join h1 h2)
  with introduce _ ==> _
  with _ . (
    assert (down_p p h1);
    let h1_ = { small = h1; big = H2.empty_heap } in
    let h2_ = { small = h2; big = H2.empty_heap } in
    let h12 = H2.join h1 h2 in
    let h12_ = {small = H2.join h1 h2; big = H2.empty_heap} in
    assert (disjoint h1_ h2_);
    ()
  )

let down (p:slprop) : small_slprop =
  down_p_affine p;
  H2.as_slprop (down_p p)
let up_p (p:small_slprop) : heap -> prop = fun h -> H2.interp p h.small
let up_p_affine (p:small_slprop)
: Lemma (heap_prop_is_affine (up_p p))
= H2.interp_depends_only_on p

let up (p:small_slprop) : slprop = up_p_affine p; F.on _ (up_p p)

let down_up (p:small_slprop)
: Lemma (down (up p) == p)
        [SMTPat (down (up p))]
= down_p_affine (up p);
  up_p_affine p;
  introduce forall h.
    H2.interp (down (up p)) h <==> H2.interp p h
  with  (
    calc (<==>) {
      H2.interp (down (up p)) h;
    (<==>) {}
      down_p (up p) h;
    (<==>) {}
      down_p (F.on _ (up_p p)) h;
    (<==>) { () }
      H2.interp p h;
    };
    ()
  );
  H2.slprop_extensionality (down (up p)) p

let h2_of_slprop (p:H2.slprop u#a) : H2.a_heap_prop u#a =
  H2.interp_depends_only_on p;
  fun h -> H2.interp p h
let big_up (p:H2.slprop u#(a + 1))
: slprop u#a
= as_slprop (fun h -> h2_of_slprop p h.big)
let up_small_is_small s = ()

(* Four main connectives *)
let emp = up H2.emp
let pure p = up (H2.pure p)
let star p1 p2 =
  as_slprop (fun (h: heap) ->
    exists (h1 h2 : heap).
        h1 `disjoint` h2 /\
        h == join h1 h2 /\
        interp p1 h1 /\
        interp p2 h2)
let h_exists #a f = as_slprop (fun h -> exists (x:a). interp (f x) h)

(* Properties of emp *)
let h_join_empty (h:heap)
  : Lemma (disjoint h empty_heap /\
           join h empty_heap == h)
           [SMTPatOr
              [[SMTPat (disjoint h empty_heap)];
               [SMTPat (join h empty_heap)]]]
  = h2_join_empty h.small;
    h2_join_empty h.big
let emp_unit p =
  introduce forall h. interp p h <==> interp (p `star` emp) h
  with (
    assert (h == join h empty_heap);
    H2.intro_emp H2.empty_heap
  )
let intro_emp h =
  assert (h == join empty_heap h);
  H2.intro_emp H2.empty_heap


(* Properties of pure *)
let pure_equiv p q = H2.pure_equiv p q
let pure_interp q h = H2.pure_interp q h.small
let pure_star_interp p q h =
  introduce interp (p `star` pure q) h ==>
            interp (p `star` emp) h /\ q
  with _ . (
    eliminate exists h0 h1.
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp p h0 /\
      interp (pure q) h1
    returns interp (p `star` emp) h /\ q
    with _ . (
      H2.pure_interp q h1.small;
      H2.intro_emp h1.small
    )
  );
  introduce interp (p `star` emp) h /\ q ==>
            interp (p `star` pure q) h            
  with _ . (
    eliminate exists h0 h1.
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp p h0 /\
      interp emp h1
    returns interp (p `star` pure q) h
    with _ . (
      pure_interp q h1
    )
  );
  ()

(* Properties of star *)
let affine_star p1 p2 h = ()
let intro_star p q h hq = ()
let elim_star p q h = ()
let star_commutative p1 p2 = ()
#push-options "--fuel 0 --ifuel 4 --z3rlimit_factor 4 --z3cliopt smt.qi.eager_threshold=1000000"
let star_associative p1 p2 p3 = ()
#pop-options
let star_congruence p1 p2 q1 q2 = ()

let interp_up_down (p:slprop) (h:heap)
: Lemma (interp p { small = h.small; big = H2.empty_heap } <==> interp (up (down p)) h)
=   calc (<==>) {
        interp (up (down p)) h;
      (<==>) {}
         up_p (down p) h;
      (<==>) {}
         H2.interp (down p) h.small;
      (<==>) {  }
         (down_p_affine p;
          H2.interp (H2.as_slprop (down_p p)) h.small);
      (<==>) {}
         down_p p h.small;
      (<==>) {}
        p {small = h.small; big = H2.empty_heap};
      }

let lift_small_star (p q:small_slprop)
: Lemma (up (p `H2.star` q) == up p `star` up q)
        [SMTPat (up (p `H2.star` q))]
= introduce forall m.
    interp (up (p `H2.star` q)) m <==>
    interp (up p `star` up q) m
  with (
    introduce 
      interp (up p `star` up q) m ==>
      interp (up (p `H2.star` q)) m
    with _ . ( 
      eliminate exists h0 h1.
        disjoint h0 h1 /\
        m == join h0 h1 /\
        interp (up p) h0 /\
        interp (up q) h1
      returns interp (up (p `H2.star` q)) m
      with _ . (
        H2.intro_star p q h0.small h1.small
      )
    );
    introduce 
      interp (up (p `H2.star` q)) m ==>
      interp (up p `star` up q) m
    with _ . ( 
      H2.elim_star p q m.small;
      eliminate exists c0 c1.
        H2.disjoint c0 c1 /\
        m.small == H2.join c0 c1 /\
        H2.interp p c0 /\
        H2.interp q c1
      returns interp (up p `star` up q) m
      with _ . (
        let h0 = { m with small = c0 } in
        let h1 = { empty_heap with small = c1 } in
        assert (join h0 h1 == m)
      )
    )
  );
  slprop_extensionality (up (p `H2.star` q)) (up p `star` up q)

let vprop_star p1 p2 =
  introduce forall h. 
    interp (p1 `star` p2) h ==> interp (up (down (p1 `star` p2))) h
  with introduce _ ==> _ 
  with _. (
    eliminate exists h1 h2. 
      disjoint h1 h2 /\
      h == join h1 h2 /\
      interp p1 h1 /\
      interp p2 h2
    returns interp (up (down (p1 `star` p2))) h
    with _ . (
      interp_up_down (p1 `star` p2) h;
      let hh = { h with big = H2.empty_heap } in
      let hh1 = {h1 with big = H2.empty_heap} in
      let hh2 = {h2 with big = H2.empty_heap} in
      assert (interp p1 hh1);
      assert (interp p2 hh2);
      assert (disjoint hh1 hh2);
      assert (interp (p1 `star` p2) hh)
    )
  );
  introduce forall h. 
    interp (up (down (p1 `star` p2))) h ==> interp (p1 `star` p2) h
  with introduce _ ==> _
  with _. (
    interp_up_down (p1 `star` p2) h;
    let hh = { h with big = H2.empty_heap } in
    assert (interp (p1 `star` p2) hh);
    eliminate exists hh0 hh1. 
      disjoint hh0 hh1 /\
      hh == join hh0 hh1 /\
      interp p1 hh0 /\
      interp p2 hh1
    returns interp (p1 `star` p2) h
    with _ . (
      assert (hh.big == H2.empty_heap);
      assert (H2.disjoint hh.big h.big);
      h2_join_empty h.big;
      H2.join_commutative hh.big h.big;
      let h0 = {hh0 with big = h.big} in
      let h1 = {hh1 with big = H2.empty_heap} in
      assert (H2.join hh.big h.big == h.big);
      assert (join h0 h1 == h);
      assert (interp p1 h0);
      assert (interp p2 h1)
    )
  );
  slprop_extensionality (up (down (p1 `star` p2))) (p1 `star` p2)

let h_exists_cong #a p q = ()
let intro_h_exists x p h = ()
let elim_h_exists #a p h = ()
#restart-solver
let vprop_exists_alt (a:Type) (p:a -> slprop)
: Lemma 
  (requires forall x. is_small (p x))
  (ensures is_small (h_exists p))
= introduce forall h.
    interp (h_exists p) h ==> interp (up (down (h_exists p))) h
  with introduce _ ==> _
  with _ . (
    interp_up_down (h_exists p) h;
    eliminate exists x.
      interp (p x) h
    returns interp (up (down (h_exists p))) h
    with _ . (
      interp_up_down (p x) h
    )
  );
  introduce forall h.
    interp (up (down (h_exists p))) h ==> interp (h_exists p) h
  with introduce _ ==> _ 
  with _ . (
    interp_up_down (h_exists p) h;
    eliminate exists x.
      interp (up (down (p x))) h
    returns interp (h_exists p) h
    with _ . (
      interp_up_down (p x) h
    )
  );
  slprop_extensionality (h_exists p) (up (down (h_exists p)));
  ()
let vprop_exists (a:Type) (p:a -> vprop)
: Lemma (is_small (h_exists p))
= vprop_exists_alt a p

let stronger_star p q r = ()
let weaken p q r h = ()


let full_heap_pred h =
  H2.full_heap_pred h.small /\
  H2.full_heap_pred h.big
let heap_evolves (h0 h1:full_heap) =
  H2.heap_evolves h0.small h1.small /\
  H2.heap_evolves h0.big h1.big
let free_above_addr tag h a = H2.free_above_addr tag h.small a /\ H2.free_above_addr tag h.big a
let weaken_free_above tag h a b = H2.weaken_free_above tag h.small a b; H2.weaken_free_above tag h.big a b

let up_pred (pre:H2.heap u#a -> prop)
  : heap -> prop
  = fun h -> pre h.small

let up_pre_action
      (#pre #post:_) (#fp:small_slprop) (#a:Type) (#fp':a -> small_slprop)
      (act:H2.pre_action #pre #post fp a fp')
: pre_action #(up_pred pre) #(up_pred post) (up fp) a (fun x -> up (fp' x))
= fun (h0:full_hheap (up fp) { up_pred pre h0 }) ->
    let (| x, c |) = act h0.small in
    let h1 : full_hheap (up (fp' x)) = { h0 with small=c } in
    (| x, h1 |)

let heap_evolves_iff (h0 h1:full_heap)
: Lemma 
  (ensures
     heap_evolves h0 h1 <==> (
      H2.heap_evolves h0.small h1.small /\
      H2.heap_evolves h0.big h1.big))
= assert (heap_evolves h0 h1 <==> 
            (H2.heap_evolves h0.small h1.small /\ H2.heap_evolves h0.big h1.big))
      by (FStar.Tactics.norm [delta_only [`%heap_evolves]])

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
let up_action
      (#mut #allocs :_)
      (#pre #post:_)
      (#fp:small_slprop) (#a:Type) (#fp':a -> small_slprop)
      (act:H2.action #mut #allocs #pre #post fp a fp')
: action #mut #allocs #(up_pred pre) #(up_pred post)
        (up fp) a (fun x -> up (fp' x))
= let p = up_pre_action act in
  introduce forall frame (h0:full_hheap (up fp `star` frame) { up_pred pre h0 }).
    let (| x, h1 |) = p h0 in
    interp (up (fp' x) `star` frame) h1 /\
    action_related_heaps #mut #allocs h0 h1
  with (
    assert (interp (up fp `star` frame) h0);
    let (| x, h1 |) = p h0 in
    eliminate exists h0' h1'.
      disjoint h0' h1' /\
      h0 == join h0' h1' /\
      interp (up fp) h0' /\
      interp frame h1'
    returns 
      interp (up (fp' x) `star` frame) h1 /\
      action_related_heaps #mut #allocs h0 h1
    with _ . (
      let hframe : H2.heap -> prop = (fun h -> interp frame { small = h; big = h1'.big }) in
      introduce forall c0 c1.
        (hframe c0 /\ H2.disjoint c0 c1)
         ==> 
        hframe (H2.join c0 c1)
      with (
        introduce _ ==> _
        with _ . (
          let h0g = {small=c0; big=h1'.big} in
          assert (interp frame h0g);
          assert (H2.disjoint c0 c1);
          assert (heap_prop_is_affine frame);
          let h1g = { small = c1; big = H2.empty_heap } in
          assert (disjoint h0g h1g);
          assert (interp frame (join h0g h1g));
          assert (hframe (H2.join c0 c1))
        )
      );
      assert (H2.heap_prop_is_affine hframe);
      let hframe : H2.slprop = H2.as_slprop hframe in
      assert (H2.interp fp h0'.small);
      assert (H2.interp hframe h1'.small);
      H2.intro_star fp hframe h0'.small h1'.small;
      let h00 : H2.full_hheap (fp `H2.star` hframe) = h0.small in
      let h11 : H2.full_hheap (fp' x `H2.star` hframe) = dsnd (act h00) in
      assert (h1 == { h0 with small = h11 });
      H2.elim_star (fp' x) hframe h11;
      eliminate exists c0 c1.
        H2.disjoint c0 c1 /\
        h11 == H2.join c0 c1 /\
        H2.interp (fp' x) c0 /\
        H2.interp hframe c1
      returns interp (up (fp' x) `star` frame) h1
      with _ . ( 
        let h10 = { small = c0; big = h0'.big } in
        let h11 = { small = c1; big = h1'.big } in
        assert (interp (up (fp' x)) h10);
        assert (interp frame h11);
        assert (disjoint h10 h11)
      );
      heap_evolves_iff h0 h1;
      assert (action_related_heaps #mut #allocs h0 h1)
    )
  );
  p
let up_action_big_heap_immutable
    (#mut #allocs #pre #post:_)
    (#fp:small_slprop) (#a:Type) (#fp':a -> small_slprop)
    (act:H2.action #mut #allocs #pre #post fp a fp')
    (h0:full_hheap (up fp) { up_pred pre h0 })
: Lemma (
    let (|x, h1|) = up_action act h0 in
    h1.big == h0.big
  )
= ()

let refined_pre_action (#mut:mutability) (#allocates:option tag)
                       (#[T.exact (`trivial_pre)]pre:heap ->prop)
                       (#[T.exact (`trivial_pre)]post:heap -> prop)
                       (fp0:slprop) (a:Type) (fp1:a -> slprop) =
  m0:full_hheap fp0 ->
  Pure (x:a &
        full_hheap (fp1 x))
       (requires pre m0)
       (ensures fun  (| x, m1 |) ->
         post m1 /\
         (forall frame. frame_related_heaps m0 m1 fp0 (fp1 x) frame mut allocates))

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


let elim_exists #a p =
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
let lift_exists (#a:_) (p:a -> slprop)
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
#push-options "--print_universes"
let elim_pure p = up_action (H2.elim_pure p)
let intro_pure p pf = up_action (H2.intro_pure p pf)
let drop p
= let f
    : refined_pre_action p unit (fun _ -> emp)
    = fun h ->
        introduce forall h. interp emp h with intro_emp h;
        (| (), h |)
  in
  refined_pre_action_as_action f
let pts_to #a #pcm (r:ref a pcm) (v:a) = up (H2.pts_to #a #pcm r v)

let sel_action #a #pcm r v0 = up_action (H2.sel_action #a #pcm r v0)
let select_refine #a #p r x f = up_action (H2.select_refine #a #p r x f)
let upd_gen_action #a #p r x y f = up_action (H2.upd_gen_action #a #p r x y f)
let upd_action #a #p r v0 v1 = up_action (H2.upd_action #a #p r v0 v1)
let free_action #a #p r v0 = up_action (H2.free_action #a #p r v0)
let split_action #a #pcm r v0 v1 = up_action (H2.split_action #a #pcm r v0 v1)
let gather_action #a #pcm r v0 v1 = up_action (H2.gather_action #a #pcm r v0 v1)
let pts_to_not_null_action #a #pcm r v = up_action (H2.pts_to_not_null_action #a #pcm r v)
let extend
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:a{pcm.refine x})
  (addr:nat)
  : action
      #MUTABLE #(Some CONCRETE)
      #(fun h -> h `free_above_addr CONCRETE` addr)
      #(fun h -> h `free_above_addr CONCRETE` (addr + 1))
      emp 
      (ref a pcm)
      (fun r -> pts_to r x)
  = let extend'
      : action
          #MUTABLE #(Some CONCRETE)
          #(fun h -> h `free_above_addr CONCRETE` addr)
          #(up_pred (fun h -> h `H2.free_above_addr CONCRETE` (addr + 1)))
          emp 
          (ref a pcm)
          (fun r -> pts_to r x)
      = up_action (H2.extend #a #pcm x addr)
    in
    //we use a single freshness counter for the both small and big concrete heaps
    //so, we need to prove that after allocating in the small heap, the
    //big heap remains unchanged and so the next address is still fresh
    //for both heaps
    let ff :
        pre_action
          #(fun h -> h `free_above_addr CONCRETE` addr)
          #(fun h -> h `free_above_addr CONCRETE` (addr + 1))
          emp 
          (ref a pcm)
          (fun r -> pts_to r x)
      = fun h0 ->
          let (| y, h1 |) = extend' h0 in
          up_action_big_heap_immutable (H2.extend #a #pcm x addr) h0;
          H2.weaken_free_above CONCRETE h1.big addr (addr + 1);
          (| y, h1 |)
    in
    ff
let core_ghost_ref = H2.core_ghost_ref
let ghost_pts_to #a #pcm r v = up (H2.ghost_pts_to #a #pcm r v)
let ghost_extend
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:erased a{pcm.refine x})
  (addr:erased nat)
: action #ONLY_GHOST #(Some GHOST)
    #(fun h -> h `free_above_addr GHOST` addr)
    #(fun h -> h `free_above_addr GHOST` (addr + 1))      
    emp 
    (ghost_ref pcm)
    (fun r -> ghost_pts_to r x)
= let extend'
  : action #ONLY_GHOST #(Some GHOST)
    #(fun h -> h `free_above_addr GHOST` addr)
    #(up_pred (fun h -> h `H2.free_above_addr GHOST` (addr + 1)) )     
    emp 
    (ghost_ref pcm)
    (fun r -> ghost_pts_to r x)
    = up_action (H2.ghost_extend #a #pcm x addr)
  in
  let ff :
      pre_action
        #(fun h -> h `free_above_addr GHOST` addr)
        #(fun h -> h `free_above_addr GHOST` (addr + 1))
        emp 
        (ghost_ref pcm)
        (fun r -> ghost_pts_to r x)
    = fun h0 ->
        let (| y, h1 |) = extend' h0 in
        up_action_big_heap_immutable (H2.ghost_extend #a #pcm x addr) h0;
        H2.weaken_free_above GHOST h1.big addr (addr + 1);
        (| y, h1 |)
  in
  ff
let ghost_read #a #p r x f = up_action (H2.ghost_read #a #p r x f)
let ghost_write #a #p r x y f = up_action (H2.ghost_write #a #p r x y f)
let ghost_share #a #p r v0 v1 = up_action (H2.ghost_share #a #p r v0 v1)
let ghost_gather #a #pcm r v0 v1 = up_action (H2.ghost_gather #a #pcm r v0 v1)

let big_pts_to #a #pcm (r:ref a pcm) (v:a) = big_up (H2.pts_to #a #pcm r v)
let big_slprop = H2.slprop u#(a + 1)
let lift_big_emp ()
: Lemma (emp == big_up H2.emp)
= introduce forall h. H2.interp H2.emp h
  with H2.intro_emp h;
  slprop_extensionality emp (big_up H2.emp)

let lift_big_star (p q:big_slprop)
: Lemma (big_up (p `H2.star` q) == big_up p `star` big_up q)
        [SMTPat (big_up (p `H2.star` q))]
= introduce forall m.
    interp (big_up (p `H2.star` q)) m <==>
    interp (big_up p `star` big_up q) m
  with (
    introduce 
      interp (big_up p `star` big_up q) m ==>
      interp (big_up (p `H2.star` q)) m
    with _ . ( 
      eliminate exists h0 h1.
        disjoint h0 h1 /\
        m == join h0 h1 /\
        interp (big_up p) h0 /\
        interp (big_up q) h1
      returns interp (big_up (p `H2.star` q)) m
      with _ . (
        H2.intro_star p q h0.big h1.big
      )
    );
    introduce 
      interp (big_up (p `H2.star` q)) m ==>
      interp (big_up p `star` big_up q) m
    with _ . ( 
      H2.elim_star p q m.big;
      eliminate exists c0 c1.
        H2.disjoint c0 c1 /\
        m.big == H2.join c0 c1 /\
        H2.interp p c0 /\
        H2.interp q c1
      returns interp (big_up p `star` big_up q) m
      with _ . (
        let h0 = { m with big = c0 } in
        let h1 = { empty_heap with big = c1 } in
        assert (join h0 h1 == m)
      )
    )
  );
  slprop_extensionality (big_up (p `H2.star` q)) (big_up p `star` big_up q)

let big_up_pred (pre:H2.heap u#(a + 1) -> prop)
  : heap u#a -> prop
  = fun h -> pre h.big

let big_up_pre_action
      (#pre #post:_) (#fp:big_slprop) (#a:Type) (#fp':a -> big_slprop)
      (act:H2.pre_action #pre #post fp a fp')
: pre_action #(big_up_pred pre) #(big_up_pred post) (big_up fp) a (fun x -> big_up (fp' x))
= fun (h0:full_hheap (big_up fp) { big_up_pred pre h0 }) ->
    let (| x, c |) = act h0.big in
    let h1 : full_hheap (big_up (fp' x)) = { h0 with big=c } in
    (| x, h1 |)

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
let big_up_action
      (#mut #allocs #pre #post:_)
      (#fp:big_slprop) (#a:Type) (#fp':a -> big_slprop)
      (act:H2.action #mut #allocs #pre #post fp a fp')
: action #mut #allocs #(big_up_pred pre) #(big_up_pred post)
        (big_up fp) a (fun x -> big_up (fp' x))
= let p = big_up_pre_action act in
  introduce forall frame (h0:full_hheap (big_up fp `star` frame) { big_up_pred pre h0 }).
    let (| x, h1 |) = p h0 in
    interp (big_up (fp' x) `star` frame) h1 /\
    action_related_heaps #mut #allocs h0 h1
  with (
    assert (interp (big_up fp `star` frame) h0);
    let (| x, h1 |) = p h0 in
    eliminate exists h0' h1'.
      disjoint h0' h1' /\
      h0 == join h0' h1' /\
      interp (big_up fp) h0' /\
      interp frame h1'
    returns 
      interp (big_up (fp' x) `star` frame) h1 /\
      action_related_heaps #mut #allocs h0 h1
    with _ . (
      let hframe : H2.heap -> prop = (fun h -> interp frame { h1' with big = h }) in
      introduce forall c0 c1.
        (hframe c0 /\ H2.disjoint c0 c1)
         ==> 
        hframe (H2.join c0 c1)
      with (
        introduce _ ==> _
        with _ . (
          let h0g = {h1' with big=c0} in
          assert (interp frame h0g);
          assert (H2.disjoint c0 c1);
          assert (heap_prop_is_affine frame);
          let h1g = { big = c1; small = H2.empty_heap } in
          assert (disjoint h0g h1g);
          assert (interp frame (join h0g h1g));
          assert (hframe (H2.join c0 c1))
        )
      );
      assert (H2.heap_prop_is_affine hframe);
      let hframe : H2.slprop = H2.as_slprop hframe in
      assert (H2.interp fp h0'.big);
      assert (H2.interp hframe h1'.big);
      H2.intro_star fp hframe h0'.big h1'.big;
      let h00 : H2.full_hheap (fp `H2.star` hframe) = h0.big in
      let h11 : H2.full_hheap (fp' x `H2.star` hframe) = dsnd (act h00) in
      assert (h1 == { h0 with big = h11 });
      H2.elim_star (fp' x) hframe h11;
      eliminate exists c0 c1.
        H2.disjoint c0 c1 /\
        h11 == H2.join c0 c1 /\
        H2.interp (fp' x) c0 /\
        H2.interp hframe c1
      returns interp (big_up (fp' x) `star` frame) h1
      with _ . ( 
        let h10 = { h0' with big = c0 } in
        let h11 = { h1' with big = c1 } in
        assert (interp (big_up (fp' x)) h10);
        assert (interp frame h11);
        assert (disjoint h10 h11)
      );
      heap_evolves_iff h0 h1;
      assert (action_related_heaps #mut #allocs h0 h1)
    )
  );
  p
let big_up_action_small_heap_immutable
    (#mut #allocs #pre #post:_)
    (#fp:big_slprop) (#a:Type) (#fp':a -> big_slprop)
    (act:H2.action #mut #allocs #pre #post fp a fp')
    (h0:full_hheap (big_up fp) { big_up_pred pre h0 })
: Lemma (
    let (|x, h1|) = big_up_action act h0 in
    h1.small == h0.small
  )
= ()

let big_sel_action #a #pcm r v0 = big_up_action (H2.sel_action #a #pcm r v0)
let big_select_refine #a #p r x f = big_up_action (H2.select_refine #a #p r x f)
let big_upd_gen_action #a #p r x y f = big_up_action (H2.upd_gen_action #a #p r x y f)
let big_upd_action #a #p r v0 v1 = big_up_action (H2.upd_action #a #p r v0 v1)
let big_free_action #a #p r v0 = big_up_action (H2.free_action #a #p r v0)
let big_split_action #a #pcm r v0 v1 = big_up_action (H2.split_action #a #pcm r v0 v1)
let big_gather_action #a #pcm r v0 v1 = big_up_action (H2.gather_action #a #pcm r v0 v1)
let big_pts_to_not_null_action #a #pcm r v = big_up_action (H2.pts_to_not_null_action #a #pcm r v)
let big_extend
  (#a:Type u#(ua + 1))
  (#pcm:pcm a)
  (x:a{pcm.refine x})
  (addr:nat)
  : action
      #MUTABLE #(Some CONCRETE)
      #(fun h -> h `free_above_addr CONCRETE` addr)
      #(fun h -> h `free_above_addr CONCRETE` (addr + 1))
      emp 
      (ref a pcm)
      (fun r -> big_pts_to r x)
  = lift_big_emp ();
    let extend'
      : action
          #MUTABLE #(Some CONCRETE)
          #(fun h -> h `free_above_addr CONCRETE` addr)
          #(big_up_pred (fun h -> h `H2.free_above_addr CONCRETE` (addr + 1)))
          emp 
          (ref a pcm)
          (fun r -> big_pts_to r x)
      = big_up_action (H2.extend #a #pcm x addr)
    in
    //we use a single freshness counter for the both small and big concrete heaps
    //so, we need to prove that after allocating in the small heap, the
    //big heap remains unchanged and so the next address is still fresh
    //for both heaps
    let ff :
        pre_action
          #(fun h -> h `free_above_addr CONCRETE` addr)
          #(fun h -> h `free_above_addr CONCRETE` (addr + 1))
          emp 
          (ref a pcm)
          (fun r -> big_pts_to r x)
      = fun h0 ->
          let (| y, h1 |) = extend' h0 in
          big_up_action_small_heap_immutable (H2.extend #a #pcm x addr) h0;
          H2.weaken_free_above CONCRETE h1.small addr (addr + 1);
          (| y, h1 |)
    in
    ff

let big_ghost_pts_to #a #pcm r v = big_up (H2.ghost_pts_to #a #pcm r v)
let big_ghost_extend
  (#a:Type u#(ua + 1))
  (#pcm:pcm a)
  (x:erased a{pcm.refine x})
  (addr:erased nat)
: action #ONLY_GHOST #(Some GHOST)
    #(fun h -> h `free_above_addr GHOST` addr)
    #(fun h -> h `free_above_addr GHOST` (addr + 1))      
    emp 
    (ghost_ref pcm)
    (fun r -> big_ghost_pts_to r x)
= lift_big_emp ();
  let extend'
  : action #ONLY_GHOST #(Some GHOST)
    #(fun h -> h `free_above_addr GHOST` addr)
    #(big_up_pred (fun h -> h `H2.free_above_addr GHOST` (addr + 1)) )     
    emp 
    (ghost_ref pcm)
    (fun r -> big_ghost_pts_to r x)
    = big_up_action (H2.ghost_extend #a #pcm x addr)
  in
  let ff :
      pre_action
        #(fun h -> h `free_above_addr GHOST` addr)
        #(fun h -> h `free_above_addr GHOST` (addr + 1))
        emp 
        (ghost_ref pcm)
        (fun r -> big_ghost_pts_to r x)
    = fun h0 ->
        let (| y, h1 |) = extend' h0 in
        big_up_action_small_heap_immutable (H2.ghost_extend #a #pcm x addr) h0;
        H2.weaken_free_above GHOST h1.small addr (addr + 1);
        (| y, h1 |)
  in
  ff
let big_ghost_read #a #p r x f = big_up_action (H2.ghost_read #a #p r x f)
let big_ghost_write #a #p r x y f = big_up_action (H2.ghost_write #a #p r x y f)
let big_ghost_share #a #p r v0 v1 = big_up_action (H2.ghost_share #a #p r v0 v1)
let big_ghost_gather #a #pcm r v0 v1 = big_up_action (H2.ghost_gather #a #pcm r v0 v1)
