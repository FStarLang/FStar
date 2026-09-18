module CAbbrevArity

(* Section 26, item 2: a result type behind two layers of abbreviation.

   [Extract]'s [peel] consumes one arrow per extra lambda binder the body
   opened, and it unfolded abbreviations only on the way in.  [eq_test] unfolds
   to [restricted_t t (fun x1 -> eq_test_for x1)] -- one arrow whose codomain
   is *another* abbreviation -- so peeling two binders consumed the first arrow,
   landed on [eq_test_for], and stopped.  The second binder was still emitted,
   and the definition was declared to return [bool -> bool] over a body of type
   [bool].

   That is a constraint violation C compilers disagree about: gcc 13 accepts it
   with -Wint-conversion and the program happens to print the right answer,
   because a bool round-trips through a pointer on that ABI.  gcc 14 rejects it.
   Either way the declaration was a lie, and [peel] now unfolds at every step.

   This is [CDDL.Spec.EqTest.eq_test] verbatim, which is why it is worth having
   by name. *)

module FE = FStar.FunctionalExtensionality

let eq_test_for (#t: Type) (x1: t) : Type = FE.restricted_t t (fun _ -> bool)
let eq_test (t: Type) : Type = FE.restricted_t t (fun x1 -> eq_test_for x1)

let mk_eq_test (#t: Type) ([@@@monomorphize]phi: (t -> t -> bool)) : eq_test t =
  FE.on_dom t (fun x1 -> FE.on_dom t (fun x2 -> phi x1 x2))

let band (a: bool) (b: bool) : bool = a && b

let e : eq_test bool = mk_eq_test band

let ck (b: bool) : FStar.UInt32.t = if b then 0ul else 1ul

let main () : FStar.UInt32.t =
  FStar.UInt32.logor (ck (e true true)) (ck (not (e true false)))
