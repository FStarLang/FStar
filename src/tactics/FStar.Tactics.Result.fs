#light "off"
module FStar.Tactics.Result

// This file *is* extracted (unlike its twin in ulib).

// This refers to FStar.Tactics.Types.fsi in the current folder, which has the
// full definition of all relevant types (from ulib, we use an different
// interface that hides those definitions).
open FStar.Tactics.Types

type __result<'a> =
    | Success of 'a * proofstate
    | Failed  of exn       //error
              * proofstate //the proofstate at time of failure
