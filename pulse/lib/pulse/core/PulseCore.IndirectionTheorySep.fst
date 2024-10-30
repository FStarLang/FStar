module PulseCore.IndirectionTheorySep
module I = PulseCore.IndirectionTheorySepImpl
open FStar.Ghost
module PropExt = FStar.PropositionalExtensionality

noeq type istore = {
  ist: (is:I.istore { I.istore_slprops_ok is });
  saved_credits: erased nat;
  freshness_counter: nat;
}

noeq type core_istore = {
  ist: (is:I.istore { I.istore_slprops_ok is });
  saved_credits: erased nat;
}

// let to_core (w: I.world) : core_istore =
//   { ist = fst w; saved_credits = (snd w).saved_credits; pulse_mem = (snd w).pulse_heap }

let of_core (m: core_mem) : I.world =
  (m.istore.ist, ({ saved_credits = m.istore.saved_credits; pulse_heap = m.pulse_mem } <: I.rest))

let istore_core i = { ist = i.ist; saved_credits = i.saved_credits }

let age1 k =
  { k with istore = { k.istore with ist = I.age1_istore k.istore.ist } }

let slprop = I.slprop

let level k = I.level_istore k.istore.ist

let credits k = k.saved_credits

let is_ghost_action_istore = admit ()

let update_ghost = admit ()

let emp = I.emp
let pure = I.pure
let star = I.star

let (exists*) #a f = I.((exists*)) f

let sep_laws = I.sep_laws

let istore_disjoint i0 i1 = I.disjoint_istore i0.ist i1.ist

let istore_join i0 i1 =
  { ist = I.join_istore i0.ist i1.ist; saved_credits = i0.saved_credits + i1.saved_credits }

let istore_join_refl i = I.join_istore_refl i.ist

let interp p =
  introduce forall (m0 m1:core_mem). p (of_core m0) /\ disjoint m0 m1 ==> p (of_core (join m0 m1)) with
    introduce _ ==> _ with _.  assert I.world_le (of_core m0) (of_core (join m0 m1));
  fun m -> p (of_core m)

let star_equiv p q m = admit ()

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
let lower_inames = admit()

let istore_inames_ok e m = admit ()

let inames_ok_empty m = admit ()
let inames_ok_union m = admit ()