module OffEscapeHatch
open OffInt
open OffBool

(* With `--ext fstar:overload=off` there is no candidate collection at
   all: `f` is OffBool.f and nothing else, so applying it to an int is a
   plain type error. This is exactly what F* did before overloading, and
   it is what this option is for. *)
[@@expect_failure]
let a : int = f 0

(* The name that first-match-wins resolution picks still works. *)
let b : bool = f true

(* Qualification is still the way to reach the shadowed one. *)
let c : int = OffInt.f 0
