module IncompatibleQuals

(* cannot inline an assumed definition. *)
[@@expect_failure [162]]
assume
inline_for_extraction
val x : int

(* Projectors are declaration-only, but they do get code at extraction
time, so `inline_for_extraction` on the inductive is fine. *)
inline_for_extraction
type r1 = { 
 x:int; b:int;
}

(* similar for discriminators *)
inline_for_extraction
type var1 =
 | A1 | B1

(* cannot assume a definition *)
[@@expect_failure [162]]
assume
type t = unit
