module FStarC.Tactics.Common

(* NOTE: This file is exactly the same as its .fs/.fsi counterpart.
It is only here so the equally-named interface file in ulib/ is not
taken by the dependency analysis to be the interface of the .fs. We also
cannot ditch the .fs, since out bootstrapping process does not extract
any .ml file from an interface. Hence we keep both, exactly equal to
each other. *)

open FStarC.Syntax.Syntax

exception NotAListLiteral
exception TacticFailure of FStarC.Errors.Msg.error_message & option FStarC.Range.t
exception EExn of term
exception SKIP (* used by ctrl_rewrite *)

(* NOTE: There is an extraction rule to turn

  the user `FStar.Stubs.Tactics.Common.Stop` into the internal `FStarC.Errors.Stop` *)
