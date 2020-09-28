module FStar.Tactics.Common

(* This module is realized by FStar.Tactics.Common in the F* sources.
Any change must be reflected there. *)

exception NotAListLiteral

(* We should attempt to not use this one and define more exceptions
above. *)
exception TacticFailure of string
