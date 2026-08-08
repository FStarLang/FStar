(*
   `M?.reflect e` must not be allowed to claim an arbitrary specification.

   On master, a user-defined layered effect's representation is *indexed by its
   specification*, so `reflect` has to discharge that specification: master
   rejects

       M?.reflect (fun () -> ()) : M unit (ensures fun _ -> False)

   with `Error 19: Assertion failed / could not prove post-condition`.

   The `gebner_simple_effects` branch deleted the code in
   src/typechecker/FStarC.TypeChecker.TcTerm.fst (the `Tm_constant
   (Const_reflect l)` case, ~line 1141) that read the effect indices off the
   representation type, replacing it with a hard-coded trivial spec:

       (* Reflection gives back a computation with a trivial specification:
          effect definitions play no role in typechecking. *)
       comp_pre  = S.trivial_pre;
       comp_post = S.trivial_post a;

   and the user-written computation type is then adopted verbatim.  The
   `reify` path (~line 1090) has the same shape.  This is structural, not a
   bypass: the branch cannot express a spec-indexed repr at all -- such a
   declaration is rejected with `Error 189` / `Error 187` -- so master's
   soundness mechanism is *removed* rather than merely evaded.

   Consequences on the branch:
     * `reify (boom ())` yields `squash False` with EXIT=0 under
       `--warn_error '@1..1000' --report_assumes error`; there is no `admit`,
       no `assume`, and `total` on the effect declaration suppresses even
       Warning 272.
     * The resulting `val contradiction : squash False` can be exported through
       an `.fsti`, cached to a `.checked` file, and consumed by another module
       with NO warning and NO error.
     * After extraction, `let escaped : (r:int{r == 1}) = reify (use ())`
       evaluates to 0 -- a runtime refinement violation.

   Both `expect_failure`s below MUST be rejected.  NOTE: this file cannot be
   run on master, which rejects the index-free effect declaration outright
   (`Error 168: unexpected empty binders list in the layered effect
   definition`); the master-side companion is a spec-indexed repr, which master
   accepts for an honest spec and rejects for a lying one.

   Related and PRE-EXISTING (reproduces identically on master, report
   separately): `ulib/FStar.Tactics.Effect.fsti` marks `TAC` reflectable while
   `tac_repr` ignores its `wp` index, so
       let liar () : TacH unit (ensures fun _ -> False) = TAC?.reflect (fun _ -> ())
       let bogus () : Tac (n:nat{n < 10}) = let _ = liar () in 999
   is accepted by BOTH binaries and really returns 999.  On master that is
   fixable by making `wp` a real index; on this branch it is not.
*)
module SimpleEffects_ReflectSpec

let id_repr (a:Type) : Type = a
let id_return (a:Type) (x:a) : id_repr a = x
let id_bind (a b:Type) (f:id_repr a) (g:a -> id_repr b) : id_repr b = g f

total reifiable reflectable effect {
  M with { repr = id_repr; return = id_return; bind = id_bind }
}

/// `reflect` must not be able to invent a false postcondition.
[@@ expect_failure]
let liar1 () : M unit (requires True) (ensures fun _ -> False) = M?.reflect ()

/// ... nor a postcondition the reflected value does not satisfy.
[@@ expect_failure]
let liar2 () : M int (requires True) (ensures fun r -> r == 1) = M?.reflect 0

/// Reflection at the trivial specification must keep working.
let honest () : M int (requires True) (ensures fun _ -> True) = M?.reflect 0

/// `reflect` justifies only the trivial specification, so a nontrivial claim
/// has to be carried by the *result type* instead -- move the postcondition
/// into a refinement, which `reflect` does check against the representation:
let honest_refined () : M (n:nat{n == 0}) (requires True) (ensures fun _ -> True) =
  M?.reflect (0 <: n:nat{n == 0})

/// ... and a refinement that the reflected value does not satisfy is rejected.
[@@ expect_failure]
let liar_refined () : M (n:nat{n == 1}) (requires True) (ensures fun _ -> True) =
  M?.reflect (0 <: n:nat{n == 1})

/// A false `ensures` is still rejected when the value is refined.
[@@ expect_failure]
let liar_ensures () : M int (requires True) (ensures fun r -> r == 1) =
  M?.reflect (0 <: n:nat{n == 0})

/// NOTE: writing the refinement in the result type and *also* asking for an
/// equivalent `ensures` at the same time does not work, because the trivial
/// computation is built at the ascribed result type (`int`), which has already
/// dropped the refinement.  Use the refined result type, as `honest_refined`
/// does.  Separately, and independently of `reflect`, result-type subtyping
/// between two computations of the same user-defined effect is currently
/// rejected (`h () : M (n:nat{n == 0}) ...` used at `M int (ensures r == 0)`);
/// that is a pre-existing incompleteness on this branch, not unsoundness, and
/// it reproduces with `assume val` and no `reflect` anywhere.
