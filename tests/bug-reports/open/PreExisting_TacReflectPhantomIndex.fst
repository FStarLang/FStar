(*
   PRE-EXISTING UNSOUNDNESS -- reproduces identically on master and on the
   `gebner_simple_effects` branch with this exact source.  Filed separately
   from the branch's own effect-system regressions.

   `TAC` is declared `reflectable` in ulib/FStar.Tactics.Effect.fsti, so
   `TAC?.reflect` is available to any user.  `reflect` is sound for a layered
   effect only when the effect's specification is a real *index* of the
   representation type, so that reflecting a value forces you to discharge the
   specification you are claiming.  For `TAC` it is not:

     master:  let tac_repr (a:Type) (wp:tac_wp_t a) = ref_proofstate -> Dv a
     branch:  let tac_repr (a:Type)                 = ref_proofstate -> Dv a

   On master `wp` is a *phantom* index -- it is bound but does not occur in the
   body, so `tac_repr a wp1` and `tac_repr a wp2` are the same type, and
   `reflect` can claim any `wp` at all.  The branch simply drops the parameter,
   which is the same hole made explicit.

   Hence `liar` below reflects a trivially-succeeding metaprogram at a
   postcondition of `False`, and `bogus` uses it to return 999 at type
   `n:nat{n < 10}`.  Both binaries accept it, and both *print 999* when the
   tactic actually runs:

     TAC>> bogus () : n:nat{n < 10}  returned  999
     Verified module / All verification conditions discharged successfully

   No `admit`, no `assume`, no warning.  This is a genuine runtime type error
   in the metaprogramming layer, and `False` follows from `liar` directly.

   Note on fixability: on master this can be repaired by making `wp` a real
   index of `tac_repr` (e.g. `ref_proofstate -> Dv (v:a{...})`, or by dropping
   the `reflectable` qualifier).  On the `gebner_simple_effects` branch it
   cannot: that branch's `reflect` rule hard-codes a trivial spec and then
   adopts the user's ascription verbatim, and a spec-indexed repr is rejected
   outright (`Error 189` / `Error 187`).  See
   SimpleEffects_ReflectSpec.fst in this directory.

   Both `expect_failure`s below MUST be rejected; today neither is.
*)
module PreExisting_TacReflectPhantomIndex

open FStar.Tactics

/// Reflecting a trivially-succeeding metaprogram at a false postcondition.
[@@ expect_failure]
let liar () : TacH unit (requires True) (ensures fun _ -> False) =
  TAC?.reflect (fun _ps -> ())

/// ... which yields a value violating its own refinement at runtime.
[@@ expect_failure]
let bogus () : Tac (n:nat{n < 10}) = let _ = liar () in 999

/// Honest reflection must keep working.
let honest () : TacH unit (requires True) (ensures fun _ -> True) =
  TAC?.reflect (fun _ps -> ())
