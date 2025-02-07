module FStar.Stubs.Tactics.Common

include FStar.Stubs.Errors.Msg

(* This module is realized by FStar.Tactics.Common in the F* sources.
Any change must be reflected there. *)

exception NotAListLiteral

(* We should attempt to not use this one and define more exceptions
above. *)
exception TacticFailure of error_message & option FStar.Range.range

exception SKIP

(* This will stop the execution of the metaprogram, reporting all the errors
that have been logged so far (with log_issues). If none have been logged
F* will anyway display an error and reject the definition, but the expectation
is that this is only raised when the plugin is doing its own error handling. *)
exception Stop
