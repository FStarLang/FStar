module FStar.Tactics.Result

// This file is never extracted. It's a copy of the one with the same name in
// the compiler.  It lives here so that one doesn't need to adjust their load
// path to use tactics from ulib.

// This refers to FStar.Tactics.Types.fsti in ulib, which just has an abstract
// definition of proofstate.
open FStar.Tactics.Types

noeq type __result a =
    | Success of a * proofstate
    | Failed  of string    //error message
              * proofstate //the proofstate at time of failure
