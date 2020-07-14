module FStar.Tactics.Common

exception NoMatch
exception NotAnEquality
exception NotALemma
exception NotAListLiteral

(* We should attempt to not use this one and define more exceptions
above. *)
exception TacticFailure of string
