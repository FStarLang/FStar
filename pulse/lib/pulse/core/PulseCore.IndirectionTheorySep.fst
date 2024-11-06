module PulseCore.IndirectionTheorySep
module I = PulseCore.IndirectionTheorySepImpl
open FStar.Ghost
module PropExt = FStar.PropositionalExtensionality

let mem = I.world

let timeless_mem_of m = (snd m).timeless_heap

let age1 k = I.age1 k

let slprop = I.slprop

let level k = I.level_ k

let credits k = (snd k).saved_credits

let update_timeless_mem m p = (fst m, { snd m with I.timeless_heap = p })

let is_ghost_action =
  PM.ghost_action_preorder ();
  fun i1 i2 -> PM.is_ghost_action (timeless_mem_of i1) (timeless_mem_of i2)

let lift_ghost_action m p = ()

let update_ghost m1 m2 =
  (I.reveal_istore (fst m2), {
    I.saved_credits = (snd m2).saved_credits;
    I.timeless_heap = PM.pulse_heap_sig.update_ghost (timeless_mem_of m1) (timeless_mem_of m2);
  })

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

let disjoint m1 m2 = I.disjoint_worlds m1 m2
let join m1 m2 = I.join_worlds m1 m2

let clear_except_istore i = (fst i, I.empty_rest)

let join_refl i =
  PM.pulse_heap_sig.sep.join_empty (snd i).timeless_heap;
  I.join_istore_refl (fst i)

let disjoint_join_levels i0 i1 = ()

let interp p =
  introduce forall (m0 m1:mem). p m0 /\ disjoint m0 m1 ==> p (join m0 m1) with
    introduce _ ==> _ with _.  assert I.world_le m0 (join m0 m1);
  p

let update_timeless_mem_id m = ()
let join_update_timeless_mem m1 m2 p1 p2 = ()

let star_equiv p q m =
  introduce
    forall m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
      ==> interp (p `star` q) m
    with introduce _ ==> _ with _. (
    assert I.disjoint_worlds m0 m1;
    assert m == I.join_worlds m0 m1
  );
  introduce
    interp (p `star` q) m ==>
    exists m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
    with _. (
    assert I.star p q m;
    let (m1, m2) = I.star_elim p q m in
    assert disjoint m1 m2;
    assert m == join m1 m2
  )

let erase_pair #t #s (p: erased (t & s)) : erased t & erased s =
  (hide (fst p), hide (snd p))

let split_mem (p:slprop) (q:slprop) (m:erased mem { interp (p `star` q) m })
: res:(erased mem & erased mem) {
    let l, r = res in
    disjoint l r /\
    reveal m == join l r /\
    interp p l /\
    interp q r
  }
= erase_pair (I.star_elim' p q m)
  
let intro_star (p q:slprop) (m0 m1:mem)
: Lemma
  (requires disjoint m0 m1 /\ interp p m0 /\ interp q m1)
  (ensures interp (p `star` q) (join m0 m1))
= star_equiv p q (join m0 m1)

let emp_equiv m = ()

let interp_exists p = ()

let interp_pure p m = ()

let lift p = I.lift p
let lift_eq p = ()
let lift_emp_eq () = I.lift_emp_eq ()
let lift_pure_eq p = I.lift_pure_eq p
let lift_star_eq p q = I.lift_star_eq p q

let iref = I.iref
let deq_iref = fun x y -> reveal x = reveal y
let lower_inames i = GhostSet.empty

let istore_inames_ok e m = I.inames_ok e (fst m)

let inames_ok_empty m = ()
let inames_ok_union i j m =
  assert (I.inames_ok (FStar.GhostSet.union i j) (fst m) <==>
    I.inames_ok i (fst m) /\ I.inames_ok j (fst m))

let istore_invariant ex i = I.istore_invariant ex (fst i)

let inames_ok_update_timeless_mem m p ex = ()
let istore_invariant_update_timeless_mem m p ex = ()

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
let equiv_timeless p q = I.equiv_timeless p q
let equiv_star_congr p q r = I.equiv_star_congr p q r

let intro_later p m = ()

let istore_dom m = I.istore_dom (fst m)

let pulse_ghost_action_refl m : Lemma (PM.is_ghost_action m m) [SMTPat (PM.is_ghost_action m m)] =
  PM.pulse_heap_sig.is_ghost_action_preorder ()

let age_mem m =
  let m' = I.age1_ m in
  GhostSet.lemma_equal_intro (istore_dom m) (istore_dom m'); assert istore_dom m == istore_dom m';
  m'

let age_level m = ()

let age_disjoint m0 m1 = ()

let age_hereditary p m = ()

let age_later p m = ()

let spend_mem m =
  let c = (snd m).saved_credits in
  (fst m, { snd m with I.saved_credits = if c > 0 then c - 1 else 0 })

let interp_later_credit n m = ()

let spend_lemma m = ()

let spend_disjoint m0 m1 = ()

let buy_mem n m =
  (fst m, { snd m with I.saved_credits = (snd m).saved_credits + n })
let buy_lemma n m = ()
let buy_disjoint n m0 m1 = ()

let iname_ok i m = I.iname_ok i (fst m)
let inames_ok_single i p m = ()
let iname_ok_inames_ok i m = ()
let read_inv i m = I.read_inv i (fst m)
let read_inv_equiv i m p = ()
let read_inv_disjoint i m0 m1 = ()

let add_inv_eq e i : Lemma (add_inv e i == I.add_inv e i) [SMTPat (add_inv e i)] =
  assert_norm (add_inv e i == I.add_inv e i) // why???
let single_eq i : Lemma (single i == I.single i) [SMTPat (single i)] =
  assert_norm (single i == I.single i) // why???

let mem_invariant_equiv e m i = 
  I.istore_invariant_equiv e (fst m) i;
  sep_laws()

let inames_ok_istore_dom e m = ()

let inames_ok_update e m0 m1 =
  assert forall i. GhostSet.mem i (istore_dom m0) <==> GhostSet.mem i (istore_dom m1)

// let pulse_of (m: timeless_mem) : timeless_mem = m
// let pulse_join_mem (m0: timeless_mem) (m1: timeless_mem { PM.pulse_heap_sig.sep.disjoint (pulse_of m0) (pulse_of m1) }) 
// : m:timeless_mem { pulse_of m == PM.pulse_heap_sig.sep.join (pulse_of m0) (pulse_of m1) }
// = PM.pulse_heap_sig.join_mem m0 m1

let max x y = if x > y then x else y

let inames_ok_disjoint i j mi mj = ()


let pm_mem_invariant_empty ()
: Lemma (lift (PM.mem_invariant GhostSet.empty PM.pulse_heap_sig.sep.empty) == emp)
= PM.pulse_heap_sig.empty_mem_invariant GhostSet.empty;
  lift_emp_eq ()


let mem_invariant_disjoint (e f:inames) (p0 p1:slprop) (m0 m1:mem) =
  sep_laws ();
  let p0' = (p0 `star` lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0))) in
  let p1' = (p1 `star` lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m1))) in
  I.istore_invariant_disjoint' e f p0' p1' m0 m1;
  let m = join_mem m0 m1 in
  let cm = m in
  let im = I.join_worlds m0 m1 in
  Classical.forall_intro (PM.pulse_heap_sig.sep.join_empty);
  pm_mem_invariant_empty()

let mem_invariant_age e m0 m1 = 
  introduce interp (mem_invariant e m0) m1 ==>
            interp (mem_invariant e (age_mem m0)) (age1 m1)
  with _ . (
    let m10, m11 =
      split_mem (lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0)))
                (istore_invariant e m0) m1
    in
    I.istore_invariant_age e (fst m0) (m11);
    age_hereditary (lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0))) m10;
    assert (interp (istore_invariant e (age_mem m0)) (age1 m11));
    age_disjoint m10 m11;
    intro_star (lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0)))
                (istore_invariant e (age_mem m0)) 
                (age1 m10)
                (age1 m11)
  )

let mem_invariant_spend e m = ()

let mem_invariant_buy e n m = ()

let rec mk_fresh (i: iref) (ctx: list iref) :
    Tot (j:iref { j >= i /\ fresh_wrt ctx j }) (decreases ctx) =
  match ctx with
  | [] -> i
  | c::cs -> mk_fresh (max i (c+1)) cs

let fresh_inv p m ctx =
  let f = IndefiniteDescription.indefinite_description_ghost iref fun f ->
    I.fresh_addr (fst m) f in
  let i: iref = mk_fresh f ctx in
  let m': mem = (I.fresh_inv p (fst m) i, I.empty_rest) in
  let _: squash (inv i p `star` mem_invariant (single i) m' == inv i p) =
    pm_mem_invariant_empty();
    I.istore_single_invariant (level m) i p;
    sep_laws () in
  Classical.forall_intro (PM.pulse_heap_sig.sep.join_empty);
  (| i, m' |)

let dup_inv_equiv i p = I.dup_inv_equiv i p

let invariant_name_identifies_invariant i p q m =
  I.invariant_name_identifies_invariant i p q m