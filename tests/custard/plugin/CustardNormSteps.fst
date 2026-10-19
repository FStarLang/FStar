module CustardNormSteps

(* Issue #4692.  Norm steps, under both spellings, from a --with_fstarc unit
   linked against the compiler's.  See the Makefile. *)

open FStarC.Effect

(* [weak] is not used by the compiler itself. *)
let ulib_steps : list FStar.NormSteps.norm_step =
  FStar.NormSteps.([primops; weak; delta_fully ["x"]])

(* The compiler's own constructors, which must be the compiler's type. *)
let fstarc_steps : list FStarC.NormSteps.norm_step =
  FStarC.NormSteps.([Primops; Weak; ReduceProjections])

(* [FStar.Order] is realized and [le] is not in the compiler unit, so this
   unit needs a helper module for it -- as does the Pulse plugin already
   linked into fstar.exe. *)
let le_lt : bool = FStar.Order.le FStar.Order.Lt

(* [FStar.Set] is a library module this unit compiles itself, as the Pulse
   plugin does too. *)
let in_set : bool = FStar.Set.mem 1 (FStar.Set.singleton 1)

let _ =
  FStarC.Format.print_string
    ("CustardNormSteps: " ^
     string_of_int (List.length ulib_steps + List.length fstarc_steps) ^
     (if le_lt then " le" else " gt") ^
     (if in_set then " mem" else " nomem") ^ "\n")
