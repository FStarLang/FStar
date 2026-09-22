module PrettyUnit

(* Section 73.  [FStar.Tactics.PrettifyType.entry] wraps a type in a one-field
   record and generates the round trip [T_left] / [T_right] between the two.
   When the wrapped type is itself such a wrapper over [unit] -- which is what
   an *alias* of a unit-valued CDDL rule ([null = nil]) produces -- both
   layers collapse away, and [T_left]'s body

     match x with | MkT0 y -> y

   lost its pattern to the collapse while keeping the [y] in the body.  The
   variable was left free, and the C backend refused it with error 368 while
   the karamel backend died with a bare OCaml failure.

   EverParse's COSE parser is generated this way and hit it on both legs. *)

open FStar.Tactics.PrettifyType { entry }

type ugly_nil = unit
%splice[evercddl_nil; evercddl_nil_left; evercddl_nil_right]
  (entry "evercddl_nil" (`%ugly_nil))

(* The alias.  A single wrapper is not enough: its payload is [unit] already,
   and the definition is erased before it can go wrong. *)
type ugly_null = evercddl_nil
%splice[evercddl_null; evercddl_null_left; evercddl_null_right]
  (entry "evercddl_null" (`%ugly_null))

(* The same shape over a type that survives, so the test also pins that the
   fix did not disturb the ordinary case. *)
type ugly_flag = bool
%splice[evercddl_flag; evercddl_flag_left; evercddl_flag_right]
  (entry "evercddl_flag" (`%ugly_flag))

let round_trip (b:bool) : bool = evercddl_flag_left (evercddl_flag_right b)

let main () : FStar.All.ML FStar.Int32.t =
  let _ = evercddl_null_left (evercddl_null_right (evercddl_nil_right ())) in
  if round_trip true && not (round_trip false) then 0l else 1l
