module OvlSpecific
open OvlSpecificB
open OvlSpecificA

(* [OvlSpecificA.f], taking an [a] for any [a], is the scope-order answer. An
   argument whose head is known prefers the candidate whose formal has a known
   head: [OvlSpecificB.f] on a [wrap _]. *)
let a : int = f (Wrap 1)

(* Any other known head rules [OvlSpecificB.f] out. *)
let b : bool = f 1

(* An argument of unknown type keeps the scope-order answer. *)
let c (y:int) = exists x. f x /\ x == y

(* So does an [erased a], with [a] a type variable. *)
let d (#a:Type) (x:FStar.Ghost.erased a) : bool = f x
