module PulseCore.BaseHeapSig
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
open PulseCore.Tags

let interp (p:slprop) : affine_mem_prop =
  H2.interp_depends_only_on p;
  H2.interp p
let as_slprop (p:affine_mem_prop) : q:slprop{forall h. interp q h <==> p h} =
  introduce forall (h0 h1: H2.heap u#a). p h0 /\ H2.disjoint h0 h1 ==> p (H2.join h0 h1) with
    introduce _ ==> _ with _. assert disjoint_mem h0 h1;
  H2.as_slprop p

let pure (p:prop) : slprop = as_slprop fun _ -> p

let star_equiv (p q:slprop) (m:mem u#a)
= assert (forall (m0 m1: mem u#a). disjoint_mem m0 m1 == H2.disjoint m0 m1);
  introduce interp (p `star` q) m ==>
      exists m0 m1. disjoint_mem m0 m1 /\ m == join_mem m0 m1 /\ interp p m0 /\ interp q m1 with _.
    H2.elim_star p q m;
  introduce forall m0 m1.
      disjoint_mem m0 m1 /\ m == join_mem m0 m1 /\ interp p m0 /\ interp q m1 ==>
        interp (p `star` q) m with
    introduce _ ==> _ with _.
    H2.intro_star p q m0 m1

let slprop_extensionality (p q:slprop)
: Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
        [SMTPat (p == q)]
= introduce (forall c. H2.interp p c <==> interp q c) ==> p == q with _.
  H2.slprop_extensionality p q

let star_commutative (p q: slprop u#a) : Lemma (star p q == star q p) =
  introduce forall c. interp (star p q) c <==> interp (star q p) c with (
    star_equiv p q c;
    star_equiv q p c;
    introduce forall (a b: mem u#a). disjoint_mem a b <==> disjoint_mem b a with H2.disjoint_sym a b;
    introduce forall (h0 h1: mem u#a). disjoint_mem h0 h1 ==> disjoint_mem h1 h0 /\ join_mem h0 h1 == join_mem h1 h0 with
      introduce _ ==> _ with _. H2.join_commutative h0 h1
  );
  slprop_extensionality (star p q) (star q p)

let star_associative' (p q r: slprop) (m: mem { interp (star p (star q r)) m }) :
    squash (interp (star (star p q) r) m) =
  star_equiv p (star q r) m;
  let m1 = IndefiniteDescription.indefinite_description_ghost _ fun m1 -> exists m23.
    disjoint_mem m1 m23 /\ m == join_mem m1 m23 /\ interp p m1 /\ interp (star q r) m23 in
  let m23 = IndefiniteDescription.indefinite_description_ghost _ fun m23 ->
    disjoint_mem m1 m23 /\ m == join_mem m1 m23 /\ interp p m1 /\ interp (star q r) m23 in
  star_equiv q r m23;
  let m2 = IndefiniteDescription.indefinite_description_ghost _ fun m2 -> exists m3.
    disjoint_mem m2 m3 /\ m23 == join_mem m2 m3 /\ interp q m2 /\ interp r m3 in
  let m3 = IndefiniteDescription.indefinite_description_ghost _ fun m3 ->
    disjoint_mem m2 m3 /\ m23 == join_mem m2 m3 /\ interp q m2 /\ interp r m3 in
  H2.join_associative m1 m2 m3;
  let m12 = join_mem m1 m2 in
  star_equiv p q m12;
  assert disjoint_mem m12 m3;
  star_equiv (star p q) r m

let star_associative p q r : Lemma (star (star p q) r == star p (star q r)) =
  introduce forall m. interp (star p (star q r)) m <==> interp (star (star p q) r) m with (
    introduce interp (star p (star q r)) m ==> interp (star (star p q) r) m with _. (
      star_associative' p q r m
    );
    introduce interp (star (star p q) r) m ==> interp (star p (star q r)) m with _. (
      star_commutative (star p q) r;
      star_commutative p q;
      star_commutative p (star q r);
      star_commutative q r;
      star_associative' r q p m
    )
  );
  slprop_extensionality (star p (star q r)) (star (star p q) r)

let interp_as (p:affine_mem_prop)
: Lemma (forall c. interp (as_slprop p) c == p c)
= introduce forall c. interp (as_slprop p) c == p c
  with FStar.PropositionalExtensionality.apply (interp (as_slprop p) c) (p c)

let emp_unit (p:slprop) : Lemma (p == (p `star` emp)) =
  introduce forall (h: _ { interp p h }). interp (p `star` emp) h with (
    let h2 = empty_mem in
    H2.join_empty h;
    H2.intro_emp h2;
    H2.intro_star p emp h h2
  );
  introduce forall (h: _ { interp (p `star` emp) h }). interp p h with (
    star_equiv p emp h
  );
  slprop_extensionality p (p `star` emp)

let pure_true_emp () : Lemma (pure True == emp) =
  introduce forall h. interp (pure True) h <==> interp emp h with H2.intro_emp h;
  slprop_extensionality (pure True) emp
let intro_emp (h:mem) : Lemma (interp emp h) = H2.intro_emp h
let pure_interp (p:prop) (c:mem) : Lemma (interp (pure p) c == p) =
  H2.pure_interp p c; PropositionalExtensionality.apply (interp (pure p) c) p
let core_ghost_ref_is_null (r:core_ghost_ref) = H2.core_ghost_ref_is_null r
let core_ghost_ref_as_addr (r:core_ghost_ref)
: GTot nat
= H2.core_ghost_ref_as_addr r
let addr_as_core_ghost_ref (a:nat)
: GTot core_ghost_ref
= H2.addr_as_core_ghost_ref a
let core_ghost_ref_as_addr_injective r1 = H2.core_ghost_ref_as_addr_injective r1
let addr_as_core_ghost_ref_injective a = H2.addr_as_core_ghost_ref_injective a
let select_ghost i m = H2.select_ghost i m

(* Lifting H2 actions *)
let mg_of_mut (m:Tags.mutability) =
  match m with
  | Tags.MUTABLE -> false
  | _ -> true

let lower' (frame: slprop) (m: mem) (h: H2.heap) : prop =
  interp frame h
let lower (frame: slprop) (m: mem) : p:H2.slprop { forall h. H2.interp p h <==> lower' frame m h } =
  introduce forall (h0 h1: H2.heap). lower' frame m h0 /\ H2.disjoint h0 h1 ==> lower' frame m (H2.join h0 h1) with
    introduce _ ==> _ with _ . (
      assert disjoint_mem h0 h1
    );
  H2.as_slprop (lower' frame m)

let ac_lemmas ()
: Lemma (
    (forall (p q r : slprop u#a). (p `star` q) `star` r == p `star` (q `star` r)) /\
    (forall (p q: slprop u#a). p `star` q == q `star` p) /\
    (forall (p: slprop u#a). p `star` emp == p)
)
= FStar.Classical.forall_intro_3 (star_associative u#a);
  FStar.Classical.forall_intro_2 (star_commutative u#a);
  FStar.Classical.forall_intro (emp_unit u#a)

let destruct_star_l (p q:slprop) (m:mem)
: Lemma (interp (p `star` q) m ==> interp p m)
= star_equiv p q m

let destruct_star (p q:slprop u#a) (m:mem)
: Lemma (interp (p `star` q) m ==> interp p m /\ interp q m)
= ac_lemmas u#a ();
  destruct_star_l p q m;
  destruct_star_l q p m

let elim_init (fp: H2.slprop) (frame:slprop u#a) (m:mem)
: Lemma 
  (requires interp (fp `star` frame) m)
  (ensures H2.interp fp m /\ H2.interp (fp `H2.star` lower frame m) m)
= destruct_star fp frame m;
  assert H2.interp fp m;
  star_equiv fp frame m;
  let m1 = IndefiniteDescription.indefinite_description_ghost _ fun m1 -> exists m2.
    disjoint_mem m1 m2 /\ m == join_mem m1 m2 /\ interp fp m1 /\ interp frame m2 in
  let m2 = IndefiniteDescription.indefinite_description_ghost _ fun m2 ->
    disjoint_mem m1 m2 /\ m == join_mem m1 m2 /\ interp fp m1 /\ interp frame m2 in
  assert interp frame m2;
  let m3 = H2.empty_heap in
  let m4 = m2 in
  H2.join_empty m2;
  assert H2.disjoint m2 m3;
  assert disjoint_mem m2 m3;
  assert join_mem m2 m3 == m4;
  assert interp frame m4;
  assert H2.interp (lower frame m) m4;
  assert disjoint_mem m1 m4;
  assert join_mem m1 m4 == m;
  H2.intro_star fp (lower frame m) m1 m4

let intro_fin (post: H2.slprop) (frame:slprop) (m:mem)
    (m0: mem)
: Lemma
  (requires H2.interp (post `H2.star` lower frame m0) m)
  (ensures interp (post `star` frame) m)
= H2.elim_star post (lower frame m0) m;
  let h1 = IndefiniteDescription.indefinite_description_ghost _ fun h1 -> exists h2.
    H2.disjoint h1 h2 /\ m == H2.join h1 h2 /\ H2.interp post h1 /\ H2.interp (lower frame m0) h2 in
  let h2 = IndefiniteDescription.indefinite_description_ghost _ fun h2 ->
    H2.disjoint h1 h2 /\ m == H2.join h1 h2 /\ H2.interp post h1 /\ H2.interp (lower frame m0) h2 in
  let m1 = h1 in
  let m2 = h2 in
  assert interp post m1;
  let m3 = h2 in
  assert interp frame m3;
  let m4 = H2.empty_heap in
  H2.join_empty h2;
  assert disjoint_mem m3 m4;
  assert join_mem m3 m4 == m2;
  assert interp frame m2;
  assert disjoint_mem m1 m2;
  assert join_mem m1 m2 == m;
  star_equiv post frame m;
  assert interp (post `star` frame) m

let lift_heap_action
      (#fp:H2.slprop u#a)
      (#a:Type u#b)
      (#fp':a -> H2.slprop u#a)
      (#mut:_)
      ($f:H2.action #mut fp a fp')
      (#fp_post: a -> slprop u#a { forall x. fp' x == fp_post x })
: _action_except a (mg_of_mut mut) fp fp_post
= let act : _action_except a (mg_of_mut mut) fp fp_post =
    fun frame m0 ->
      elim_init fp frame m0;
      let h0 = m0 in
      assert H2.interp fp h0;
      let (| x, h1 |) = f h0 in
      assert H2.interp (fp' x) h1;
      let m1 = h1 in
      assert (H2.interp (fp' x `H2.star` lower frame m0) m1);
      assert (H2.action_related_heaps #mut h0 h1);
      intro_fin (fp' x) frame m1 m0;
      assert (maybe_ghost_action (mg_of_mut mut) m0 m1);
      (x, m1)
  in
  act

let pts_to #a #p r c = H2.pts_to #a #p r c
let ghost_pts_to #a #p r x = H2.ghost_pts_to #a #p r x

let ghost_extend #a #pcm x = fun frame m0 ->
  let (| y, m1 |) = H2.apply_action (H2.ghost_extend #a #pcm x) frame m0 in
  y, m1

let ghost_read #a #p r x f = lift_heap_action (H2.ghost_read #a #p r x f)
let ghost_write #a #p r x y f = 
  lift_heap_action (H2.ghost_write #a #p r x y f)
let ghost_share #a #p r x y =
  lift_heap_action (H2.ghost_share #a #p r x y)
let ghost_gather #a #p r x y =
  lift_heap_action (H2.ghost_gather #a #p r x y)
    #(fun _ -> ghost_pts_to r (op p x y))

let extend #a #pcm x = fun frame m0 ->
  let (| y, m1 |) = H2.apply_action (H2.extend #a #pcm x) frame m0 in
  y, m1

let read #a #p r x f = lift_heap_action (H2.select_refine #a #p r x f) #(fun v -> pts_to r (f v))
let write #a #p r x y f = 
  lift_heap_action (H2.upd_gen_action #a #p r x y f)
let share #a #p r x y =
  lift_heap_action (H2.split_action #a #p r x y)
let gather #a #p r x y =
  lift_heap_action (H2.gather_action #a #p r x y)
    #(fun _ -> pts_to r (op p x y))
let pts_to_not_null_action #a #p r x = lift_heap_action (H2.pts_to_not_null_action #a #p r x)

module U = Pulse.Lib.Raise
module R = Pulse.Lib.PCM.Raise

let ghost_pts_to' #a #p r x =
  H2.ghost_pts_to #(U.raise_t a) #(R.raise p) r (U.raise_val x)

let ghost_extend' #a #p x = fun frame m0 ->
  ghost_extend #_ #(R.raise p) (U.raise_val (reveal x)) frame m0

let ghost_read' #a #p r x f = fun frame m0 ->
  let y, m0 = ghost_read #_ #(R.raise p) r (U.raise_val (reveal x)) (R.raise_refine p x f) frame m0 in
  hide (U.downgrade_val y), m0

let ghost_write' #a #p r x y f = 
  ghost_write #_ #(R.raise p) r (U.raise_val (reveal x)) (U.raise_val (reveal y)) (R.raise_upd f)

let ghost_share' #a #p r x y =
  ghost_share #_ #(R.raise p) r (U.raise_val (reveal x)) (U.raise_val (reveal y))

let ghost_gather' #a #p r x y =
  ghost_gather #_ #(R.raise p) r (U.raise_val (reveal x)) (U.raise_val (reveal y))

let pts_to' #a #p r x =
  H2.pts_to #(U.raise_t a) #(R.raise p) r (U.raise_val x)

let extend' #a #p x = fun frame m0 ->
  extend #_ #(R.raise p) (U.raise_val x) frame m0

let read' #a #p r x f = fun frame m0 ->
  let y, m0 = read #_ #(R.raise p) r (U.raise_val (reveal x)) (R.raise_refine p x f) frame m0 in
  U.downgrade_val y, m0

let write' #a #p r x y f = 
  write #_ #(R.raise p) r (U.raise_val (reveal x)) (U.raise_val (reveal y)) (R.raise_upd f)

let share' #a #p r x y =
  share #_ #(R.raise p) r (U.raise_val (reveal x)) (U.raise_val (reveal y))

let gather' #a #p r x y =
  gather #_ #(R.raise p) r (U.raise_val (reveal x)) (U.raise_val (reveal y))

let pts_to_not_null_action' #a #p r v =
  pts_to_not_null_action #_ #(R.raise p) r (U.raise_val (reveal v))

let lift_ghost
      (#a:Type u#a)
      (#p:slprop u#b)
      (#q:a -> GTot slprop)
      (ni_a:non_info a)
      (f:erased (ghost_action_except a p q))
: ghost_action_except a p q
= fun frame m0 ->
    let xm1 : erased (a * full_mem) = 
        let ff = reveal f in
        let x, m1 = ff frame m0 in
        hide (x, m1)
    in
    let x : erased a = fst (reveal xm1) in
    let pre_m1 : erased mem = snd (reveal xm1) in
    let m1 = update_ghost m0 pre_m1 in
    let x = ni_a x in
    x, m1