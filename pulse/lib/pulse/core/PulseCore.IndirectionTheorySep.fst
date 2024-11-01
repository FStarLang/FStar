module PulseCore.IndirectionTheorySep
module I = PulseCore.IndirectionTheorySepImpl
open FStar.Ghost
module PropExt = FStar.PropositionalExtensionality

[@@erasable]
noeq type istore = {
  ist: I.okay_istore;
  saved_credits: erased nat;
}

let core_istore = istore

let to_core (w: I.world) : core_mem =
  { istore = { ist = fst w; saved_credits = (snd w).saved_credits }; pulse_mem = (snd w).pulse_heap }

let of_core (m: core_mem) : GTot I.world =
  (m.istore.ist, ({ saved_credits = m.istore.saved_credits; pulse_heap = m.pulse_mem } <: I.rest))

let istore_core i = i

let age1 k =
  { k with istore = { k.istore with ist = I.age1_istore k.istore.ist } }

let slprop = I.slprop

let ilevel k = I.level_istore k.ist
let level k = I.level_istore k.istore.ist

let level_depends_on_core_istore_only m = ()

let icredits k = k.saved_credits

let is_ghost_action_istore i1 i2 = True
  // i1.saved_credits >= i2.saved_credits /\
  // i1.freshness_counter <= i2.freshness_counter

let update_ghost m1 m2 =
  { istore = (reveal m2).istore; pulse_mem = PM.pulse_heap_sig.update_ghost m1.pulse_mem (reveal m2).pulse_mem; }

let emp = I.emp
let pure = I.pure
let star = I.star

let (exists*) #a f = I.((exists*)) #a (F.on_dom a #(fun _ -> slprop) f)

let exists_ext (#a:Type u#a) (p q : a -> slprop)
: Lemma
  (requires F.feq p q)
  (ensures op_exists_Star p == op_exists_Star q)
= ()

let sep_laws = I.sep_laws

let istore_disjoint i0 i1 = I.disjoint_istore i0.ist i1.ist

let istore_join i0 i1 =
  { ist = I.join_istore i0.ist i1.ist; saved_credits = i0.saved_credits + i1.saved_credits }

let clear_credits i =
  { i with saved_credits = 0 }

let istore_join_refl i = I.join_istore_refl i.ist

let disjoint_join_levels i0 i1 = ()

let interp p =
  introduce forall (m0 m1:core_mem). p (of_core m0) /\ disjoint m0 m1 ==> p (of_core (join m0 m1)) with
    introduce _ ==> _ with _.  assert I.world_le (of_core m0) (of_core (join m0 m1));
  fun m -> p (of_core m)

let star_equiv p q m =
  introduce
    forall m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
      ==> interp (p `star` q) m
    with introduce _ ==> _ with _. (
    let w0 = of_core m0 in
    let w1 = of_core m1 in
    assert I.disjoint_worlds w0 w1;
    assert of_core m == I.join_worlds w0 w1
  );
  introduce
    interp (p `star` q) m ==>
    exists m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
    with _. (
    let w = of_core m in
    assert I.star p q w;
    let (w1, w2) = I.star_elim p q w in
    let m1 = to_core w1 in
    let m2 = to_core w2 in
    assert disjoint m1 m2;
    assert to_core w == join m1 m2
  )

let emp_equiv m = ()

let interp_exists p = ()

let interp_pure p m = ()

let lift p = I.lift p
let lift_eq p = ()
let lift_emp_eq () = I.lift_emp_eq ()
let lift_pure_eq p = I.lift_pure_eq p
let lift_star_eq p q = I.lift_star_eq p q
let lift_exists_eq a f =
  I.world_pred_ext (lift PM.(h_exists f)) (exists* x. lift (f x)) fun _ ->
    I.lift_exists_eq a f

let iref = I.iref
let deq_iref = fun x y -> reveal x = reveal y
let lower_inames i = GhostSet.empty

let istore_inames_ok e m = I.inames_ok e m.ist

let inames_ok_iff e (m: mem) : Lemma (inames_ok e m <==> istore_inames_ok e m.istore) [SMTPat (inames_ok e m)] =
  ()

let inames_ok_empty m = ()
let inames_ok_union i j m =
  assert (I.inames_ok (FStar.GhostSet.union i j) m.istore.ist <==>
    I.inames_ok i m.istore.ist /\ I.inames_ok j m.istore.ist)

let istore_invariant ex i = I.istore_invariant ex i.ist

let mem_invariant_eq e (w:mem) : Lemma (mem_invariant e w == istore_invariant e w.istore) [SMTPat (mem_invariant e w)] =
  assume PM.mem_invariant GhostSet.empty w.pulse_mem == PM.emp;
  I.lift_emp_eq ();
  I.sep_laws ()

let inv i p = I.inv i p

let later p = I.later p
let later_credit n = I.later_credit n

let later_credit_zero = I.later_credit_zero
let later_credit_add = I.later_credit_add

let timeless_lift p = I.timeless_lift p
let timeless_pure p = I.timeless_pure p
let timeless_emp () = I.timeless_emp ()
let timeless_later_credit n = I.timeless_later_credit n
let later_star p q = I.later_star p q
let later_exists f =
  assert_norm (later (exists* x. f x) == I.(later (exists* x. f x)));
  assert_norm ((exists* x. later (f x)) == I.(exists* x. later (f x)));
  I.later_exists f

let equiv = I.equiv
let intro_equiv p m = ()
let equiv_comm p q = I.equiv_comm p q
let equiv_elim p q = I.equiv_elim p q
let equiv_trans p q r = I.equiv_trans p q r

let intro_later p m = ()

let istore_dom m = I.istore_dom m.istore.ist

let pulse_ghost_action_refl m : Lemma (PM.is_ghost_action m m) [SMTPat (PM.is_ghost_action m m)] =
  PM.pulse_heap_sig.is_ghost_action_preorder ()

let age_mem m =
  let m': mem = { m with istore = { m.istore with ist = I.age1_istore m.istore.ist } } in
  GhostSet.lemma_equal_intro (istore_dom m) (istore_dom m'); assert istore_dom m == istore_dom m';
  m'

let age_level m = ()

let age_disjoint m0 m1 = ()

let age_hereditary p m =
  assert of_core (age1 m) == I.age1_ (of_core m)

let age_later p m = ()

let spend m =
  { m with istore = { m.istore with
    saved_credits = if m.istore.saved_credits > 0 then m.istore.saved_credits - 1 else 0 } }

let spend_mem m =
  { m with istore = { m.istore with
    saved_credits = if m.istore.saved_credits > 0 then m.istore.saved_credits - 1 else 0 } }

let interp_later_credit n m = ()

let spend_lemma m = ()

let spend_disjoint m0 m1 = ()

let buy n m = { m with istore = { m.istore with saved_credits = m.istore.saved_credits + n } }
let buy_mem n m = { m with istore = { m.istore with saved_credits = m.istore.saved_credits + n } }
let buy_lemma n m = ()
let buy_disjoint n m0 m1 = ()

let iname_ok i m = I.iname_ok i m.istore.ist
let inames_ok_single i p m = ()
let iname_ok_inames_ok i m = ()
let read_inv i m = I.read_inv i m.istore.ist
let read_inv_equiv i m p = ()
let read_inv_disjoint i m0 m1 = ()

let add_inv_eq e i : Lemma (add_inv e i == I.add_inv e i) [SMTPat (add_inv e i)] =
  assert_norm (add_inv e i == I.add_inv e i) // why???
let single_eq i : Lemma (single i == I.single i) [SMTPat (single i)] =
  assert_norm (single i == I.single i) // why???

let mem_invariant_equiv e m i =
  I.istore_invariant_equiv e m.istore.ist i

let inames_ok_istore_dom e m = ()

let inames_ok_update e m0 m1 =
  assert forall i. GhostSet.mem i (istore_dom m0) <==> GhostSet.mem i (istore_dom m1)

let pulse_core_of (m: pulse_mem) : pulse_core_mem = PM.pulse_heap_sig.sep.core_of m
assume val pulse_join_mem (m0: pulse_mem) (m1: pulse_mem { PM.pulse_heap_sig.sep.disjoint (pulse_core_of m0) (pulse_core_of m1) }) :
  m:pulse_mem { pulse_core_of m == PM.pulse_heap_sig.sep.join (pulse_core_of m0) (pulse_core_of m1) }

let max x y = if x > y then x else y

let join_mem m0 m1 =
  { istore = {
    ist = I.join_istore m0.istore.ist m1.istore.ist;
    saved_credits = m0.istore.saved_credits + m1.istore.saved_credits;
  }; pulse_mem = pulse_join_mem m0.pulse_mem m1.pulse_mem }

let inames_ok_disjoint i j mi mj = ()

#push-options "--split_queries always"
let mem_invariant_disjoint e f p0 p1 m0 m1 =
  assume GhostSet.disjoint e (istore_dom m1) /\ GhostSet.disjoint f (istore_dom m0); // FIXME
  I.istore_invariant_disjoint e f m0.istore.ist m1.istore.ist;
  let m = join_mem m0 m1 in
  assert 
    mem_invariant (FStar.GhostSet.union e f) m ==
    mem_invariant e m0 `star` mem_invariant f m1;
  I.star_intro
    (p0 `star` mem_invariant e m0) (p1 `star` mem_invariant f m1)
    (of_core (core_of m)) (of_core (core_of m0)) (of_core (core_of m1));
  assert interp ((p0 `star` mem_invariant e m0) `star` (p1 `star` mem_invariant f m1)) (core_of m);
  let _: squash (p0 `star` p1 `star` mem_invariant (FStar.GhostSet.union e f) m ==
      (p0 `star` mem_invariant e m0) `star` (p1 `star` mem_invariant f m1)) =
    sep_laws () in
  assert interp (p0 `star` p1 `star` mem_invariant (FStar.GhostSet.union e f) m) (core_of m)
#pop-options

let mem_invariant_age e m0 m1 = I.istore_invariant_age e m0.istore.ist (of_core m1)
let mem_invariant_spend e m = ()

let mem_invariant_buy e n m = ()

assume val pulse_empty_mem : m:pulse_mem { pulse_core_of m == PM.pulse_heap_sig.sep.empty
  /\ forall m'. PM.pulse_heap_sig.sep.disjoint (pulse_core_of m') (pulse_core_of m) /\ pulse_join_mem m' m == m' }

let rec mk_fresh (i: iref) (ctx: list iref) :
    Tot (j:iref { j >= i /\ fresh_wrt ctx j }) (decreases ctx) =
  match ctx with
  | [] -> i
  | c::cs -> mk_fresh (max i (c+1)) cs

let fresh_inv p m ctx =
  let f = IndefiniteDescription.indefinite_description_ghost iref fun f ->
    I.fresh_addr m.istore.ist f in
  let i: iref = mk_fresh f ctx in
  let m': mem = {
    istore = {
      ist = I.fresh_inv p m.istore.ist i;
      saved_credits = 0;
    };
    pulse_mem = pulse_empty_mem;
  } in
  let _: squash (inv i p `star` mem_invariant (single i) m' == inv i p) =
    I.istore_single_invariant (level (core_of m)) i p;
    sep_laws () in
  (| i, m' |)

let dup_inv_equiv i p = I.dup_inv_equiv i p
