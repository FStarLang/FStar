module IncompatibleQuals

(* cannot inline an assumed definition. *)
[@@expect_failure [162]]
assume
inline_for_extraction
val x : int

(* inline_for_extraction means we cannot have an assumed projector, so this fails. *)
[@@no_auto_projectors; expect_failure [162]]
inline_for_extraction
type r1 = { 
 x:int; b:int;
}

(* it's fine if we omit the declarations too. *)
[@@no_auto_projectors_decls]
inline_for_extraction
type r2 = { 
 x:int; b:int;
}

(* or remove the inlining *)
[@@no_auto_projectors]
type r3 = { 
 x:int; b:int;
}

(* similar for discriminators *)
inline_for_extraction
[@@no_auto_projectors; expect_failure [162]]
type var1 =
 | A1 | B1

inline_for_extraction
[@@no_auto_projectors_decls]
type var2 =
 | A2 | B2

[@@no_auto_projectors]
type var3 =
 | A3 | B3

(* cannot assume a definition *)
[@@expect_failure [162]]
assume
type t = unit
