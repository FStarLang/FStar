# Core typechecking review notes

Review notes accompanying [Typechecking with Core](core_typechecking.md).
These record findings and proposed follow-ups; see
[Resolutions](#resolutions) for how they were addressed.

## 1. Avoid rechecking the inferred type of an unannotated let

**Location:** `src/typechecker/FStarC.TypeChecker.Core.fst`, `check_let`.

After checking `lb.lbdef` to obtain `tdef`, `check_let` uses `tdef` as
`lbtyp` when the binding has no annotation. It then unconditionally checks
`lbtyp` and extracts its universe:

```fstar
let lbtyp = if unannotated then tdef else lb.lbtyp in
let! _, ttyp = check "let type" g lbtyp in
let! u = is_type g ttyp in
```

This contradicts the preceding comment that the definition's inferred type
"needs no separate check." Checking an explicit annotation is necessary;
rechecking Core's own inferred type should not be.

The immediate purpose is to obtain the universe `u`, which is needed when
closing the body's guard (`close_with_definition`, `U.mk_forall`, and
`with_binders`). Obtaining that universe should be distinguished from
generating new well-formedness obligations for the inferred type.

Besides redundant work, rechecking may introduce obligations in the wrong
context: an inferred type can depend on facts established inside the
definition that are not available in `g`. The reference document already
explains this concern for top-level inferred types, whose separate check is
skipped using `check_t = false`. A concrete failing example for this
unannotated inner-let path has not yet been established.

**Proposed follow-up:** Use `universe_of_well_typed_term g tdef` for the
unannotated case, retaining the annotation check otherwise. That helper
computes universes mostly syntactically, but falls back to checking the
type; review whether that fallback can reintroduce the same problem before
treating this as a complete fix.

## 2. Synthesis followed by expected-type checking of a let definition

**Location:** `src/typechecker/FStarC.TypeChecker.Core.fst`, `check_let`
and `check_against_typ`.

`check_let` first synthesizes `eff_def, tdef` for the definition. For an
annotated, pushable definition (a non-recursive let, match, or abstraction),
it then tries to relate `tdef` to `lbtyp` without a guard. If that attempt
fails, it checks the definition again with `lbtyp` as its expected type.
`handle_with` catches any error from the guard-free attempt, not only a
request to emit a guard.

The second pass has a different purpose: synthesis establishes the
definition's own type, whereas expected-type checking establishes that it
meets the annotation. Pushing the expected type into the definition puts
the new obligations under local lemma facts, branch path conditions, or
function binders. Those facts need not be retained in the synthesized
result type. Relating only `tdef` and `lbtyp` in the outer environment can
therefore lose useful proof context.

For example, in `let f : t = (let _ = lemma () in f0) in body`, the goal
that `f0` meets `t` should be checked under the facts supplied by `lemma ()`.
The initial synthesis did not have `t` as an expected type and therefore
did not establish that goal there.

This explains the bidirectional check, but does not establish that two
passes are the best implementation. The initial synthesis guard remains
part of the result; the fallback adds expected-type checking rather than
replacing synthesis. The original `tdef` is also used later to enrich the
body binder's annotation with inferred refinements. The effect comparison
ensures that the fallback justifies the annotation at the effect retained
from synthesis; on a mismatch, ordinary subtyping is required as well.

**Preferred structure:** Branch on whether `lb.lbtyp` is unknown before
checking the definition:

* If unknown, synthesize the definition's type and effect, and obtain the
  inferred type's universe without a separate well-formedness check.
* Otherwise, check the annotation's well-formedness and obtain its universe,
  then call `check_against_typ g lb.lbdef lb.lbtyp` to obtain the effect.

This is the direct bidirectional structure: synthesize when there is no
annotation, check when there is one. It avoids the unconditional synthesis
pass and the speculative subtyping/fallback sequence. Both paths still
generate the obligations for the definition.

**Remaining design question:** The current implementation deliberately
retains `tdef` even for annotated bindings, using its refinements to
strengthen `x_sort` and also inspecting it for an SMT lemma type. An
annotation may have been inferred by elaboration and omit postconditions
that Core recovers from the definition. Since `check_against_typ` currently
returns only an effect, the straightforward restructuring would lose that
information. Review whether checking should additionally return the
inferred type or relevant facts, or whether binding at the annotation alone
is sufficient for the intended behavior. This information-flow question,
not the annotation obligation itself, is the reason the change needs more
than simply rearranging the existing calls.

### Addressing the design question: facts instead of binder strengthening

**Proposal:** For an annotated let, bind the variable at `lb.lbtyp` and
use facts about the checked definition to weaken the body's VC, instead
of synthesizing `tdef` solely to copy its refinement onto the binder.
This separates the binder's declared type from additional logical
information recovered while checking the definition.

For a pure or ghost definition `e`, with annotation `T`, body VC `Q(x)`,
and established facts `F(e)`, the relevant shape is:

```text
VC_definition /\ (F(e) ==> forall (x:T). x == e ==> Q(x))
```

The definition's own obligations must remain outside the weakening. With
the defining equation, a refinement fact about `e` can justify the
corresponding fact about `x` without changing `x`'s type.

`check_let` already uses this approach when it substitutes the definition
into the VC or drops the binder: it calls `term_facts`. When retaining the
binder, it instead calls `app_facts`, relying on the strengthened binder
type for the definition's own refinement.

**Points to resolve before replacing that strengthening:**

* `term_facts` is not independent of synthesis: it calls
  `type_of_checked`, which calls `check` and drops its guard under the
  assumption that the typing obligations have already been emitted.
  Removing the initial synthesis requires ensuring that expected-type
  checking establishes all facts subsequently consumed. Otherwise this
  could merely hide a second synthesis pass, or discard necessary guards.
* Facts about `e` do not automatically become facts about `x` when the
  defining equation is omitted. Preserve the connection or establish
  result facts directly about the bound value.
* An effectful definition is not a logical term denoting its result.
  `term_facts` rejects effectful computations; their postconditions must
  instead be available as facts about the bound result.
* Weakening the body's current VC alone does not preserve all information
  exported by the let. The existing synthesis path can carry the binder's
  refinement into the result type, notably when a pure definition precedes
  an effectful body. A replacement must preserve needed outgoing
  postconditions as well.
* Local SMT lemmas have a separate `smt_lemma_as_forall` path. Ordinary
  refinement/squash facts do not by themselves replace that handling.

**Direction:** Prefer the annotation-first structure above and a
clear contract for established facts about checked terms/results. For
pure definitions, VC weakening is a plausible replacement for binder
strengthening, but the current `term_facts` is not a drop-in replacement
that by itself removes synthesis.

## Resolutions

`check_let` is split into `check_let_def` (the definition),
`let_binder_sort` (the type of the bound variable), `close_let_guard`
(closing the body's guard over the variable) and `let_result_typ` (the
result type, when synthesized).

**Item 1.** For an unannotated `let`, the universe of the synthesized type
is computed by `universe_of_well_typed_term`, under `quietly`: no new
obligations are emitted for a type Core itself computed. Its fallback to
checking the type only serves to find the universe.

**Item 2.** The definition is checked in one pass, branching on whether
`lb.lbtyp` is unknown. The speculative guard-free subtyping and its
`handle_with` fallback are gone. With an annotation:

* A pure or ghost definition is checked against it (`check_against_typ`),
  so the obligations are emitted under the definition's local facts, path
  conditions and binders.
* An effectful definition has its type synthesized, then related to the
  annotation by subtyping (`check_against_typ_by_subtyping`). Pushing the
  annotation into it failed in `ulib`: an effectful computation's
  postcondition is carried only by its synthesized type, e.g. the
  branch facts of `if n < 0 then fail ""` in
  `FStar.Tactics.V2.Derived.repeatn`, which make `n` a `nat` afterwards.

The choice uses `lb.lbeff`, the elaborator's effect for the whole `let`,
which bounds the definition's. It only selects between two sound
strategies, so trusting it is not needed for soundness.

**Design question.** `check_against_typ_synth` returns the synthesized type
when it had to synthesize one (an effectful definition, or a definition
that is not pushed into). That type still refines the binder
(`let_binder_sort`) and is inspected for an SMT lemma type. When the
annotation is pushed into a pure definition, nothing is synthesized:

* The binder has the annotation as its type.
* The definition is inserted into the cache at the annotation, so that
  `term_facts` and `app_facts` find it without a second synthesis.
* What the definition establishes beyond its annotation reaches the body
  as facts: those of the definition (`app_facts`, or `term_facts` when the
  variable is substituted or dropped), and those of the expression its
  `let`s end with (`let_tail_facts`), whose type the synthesized `tdef`
  used to carry. Without the latter, `PulseCore.IndirectionTheoryActions`
  failed: `eliminate exists x. p x with star_equiv ..` elaborates to
  `let _ : unit = (let x = .. in star_equiv ..) in ..`, and only the type
  of `star_equiv ..` says what it proves. `let_tail_facts` re-synthesizes
  only that final expression, so the cost stays linear in the `let` chain.

So the effectful case keeps binder strengthening, which is the only place
its postcondition lives. The pure case uses facts plus the defining
equation, as the proposal suggested. Replacing binder strengthening for
effectful definitions with facts about the bound result is left open.

