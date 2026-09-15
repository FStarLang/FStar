module CInitTrap

(* Section 27.4: a pure, total, compile-time-constant function that was being
   compiled to mutable runtime state.

   [wrapped] is [id_fn band].  [id_fn] is saturated, so section 25's
   eta-expansion did not apply -- its arity bound only fires on an *under*
   applied head -- and [wrapped] was lowered to a [static] variable of type
   "pointer to a function from two bools to bool", assigned in
   [custard_init_globals].  (Spelling that type in C here would open a nested
   comment inside this one, which F* comments do.)

   That is worse than slow: the public entry point [use] dereferences the
   pointer, so calling it before the initializer has run is a null-pointer
   call, not a wrong answer.  Section 24
   lists [custard_init_globals] as a linking obligation; this made it a
   *memory-safety* obligation, for a definition that has no state in it.

   [id_fn] is a forwarder: its body is exactly one of its own binders, so a
   saturated call is the identity on that argument.  Reducing [id_fn band] to
   [band] leaves a definition whose body is a name, which eta-expansion already
   knows how to turn into a real function.  So [wrapped] compiles to a
   [static] function, [id_fn] dies in DCE, and the indirect call is gone from
   the caller as well.

   [direct] is the control: it always compiled correctly, and [use] must agree
   with it. *)

let id_fn (phi: (bool -> bool -> bool)) : (bool -> bool -> bool) = phi
let band (a: bool) (b: bool) : bool = a && b

(* A forwarder that returns its *second* argument, to check that the rule
   picks the right one rather than assuming there is only one binder. *)
let snd_fn (psi: (bool -> bool -> bool)) (phi: (bool -> bool -> bool))
  : (bool -> bool -> bool) = phi
let bor (a: bool) (b: bool) : bool = a || b

let direct (a: bool) (b: bool) : bool = band a b
let wrapped : bool -> bool -> bool = id_fn band
let picked : bool -> bool -> bool = snd_fn bor band

let use (a: bool) (b: bool) : bool = wrapped a b

let ck (b: bool) : FStar.UInt32.t = if b then 0ul else 1ul

let main () : FStar.UInt32.t =
  FStar.UInt32.logor
    (FStar.UInt32.logor (ck (use true true && not (use true false)))
                        (ck (direct true true && not (direct false true))))
    (ck (picked true true && not (picked true false)))
