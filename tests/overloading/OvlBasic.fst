module OvlBasic
open OvlInt
open OvlBool

(* OvlBool is opened last, so plain resolution answers OvlBool.f. The
   argument type is what recovers OvlInt.f. *)
let a : int  = f 0
let b : bool = f true

(* Discrimination on the second argument, once the first is uninformative. *)
let c : int  = g 1 2
let d : bool = g true false

(* Discrimination on the expected type alone, with no arguments at all. *)
let e : OvlInt.t  = mk 0
let h : OvlBool.t = mk true

(* A bare occurrence: only the expected type can decide. *)
let i : int -> int   = id
let j : bool -> bool = id

(* An explicitly qualified name is never overloaded. *)
let k : int = OvlInt.f 0
