#light "off"
module FStar.Tactics.Result

(* NOTE: This file is exactly the same as its .fs/.fsi counterpart.
It is only here so the equally-named interface file in ulib/ is not
taken by the dependency analysis to be the interface of the .fs. We also
cannot ditch the .fs, since out bootstrapping process does not extract
any .ml file from an interface. Hence we keep both, exactly equal to
each other. *)

// This file *is* extracted (unlike its twin in ulib).

// This refers to FStar.Tactics.Types.fsi in the current folder, which has the
// full definition of all relevant types (from ulib, we use an different
// interface that hides those definitions).
open FStar.Tactics.Types

type __result<'a> =
    | Success of 'a * proofstate
    | Failed  of exn       //error
              * proofstate //the proofstate at time of failure
