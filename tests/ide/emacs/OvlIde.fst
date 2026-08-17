module OvlIde
open OvlIdeInt
open OvlIdeBool

(* OvlIdeBool is opened last, so scope order alone answers OvlIdeBool.f;
   the argument type is what makes this OvlIdeInt.f. `f` is at column 14. *)
let a : int = f 0
