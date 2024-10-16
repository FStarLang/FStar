module FStar.Stubs.Tactics.Common

include FStar.Stubs.Errors.Msg

(* This module is realized by FStar.Tactics.Common in the F* sources.
Any change must be reflected there. *)

exception NotAListLiteral

(* We should attempt to not use this one and define more exceptions
above. *)
exception TacticFailure of error_message & option FStar.Range.range

exception SKIP
