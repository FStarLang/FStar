# Type-based overloading resolution

Single source of truth for this work: goal, design, rationale, phased plan, and progress.
Branch: `_type_based_overloading`. The original proposal is preserved verbatim in
Appendix A.

**Status: in progress.** See "Progress" at the end.

---

## 1. Goal

A function symbol `f` is resolved at desugaring time purely by name.
`DsEnv.try_lookup_id''` (DsEnv.fst:493-499) walks `env.scope_mods` **first-match-wins**:

```
let rec aux (l:list scope_mod) = match l with
  | a :: q -> option_of_cont (fun _ -> aux q) (proc a)
  | [] -> option_of_cont (fun _ -> None) (lookup_default_id Cont_fail id)
```

`scope_mods` is innermost-first, so the most recent `open` silently shadows earlier ones.
Disambiguating therefore requires explicit module qualification, or module authors picking
globally distinct names. We want the choice to be informed by types.

F* already does type-based disambiguation for constructors and projectors
(`Unresolved_constructor`, `Unresolved_projector`). We generalize it to all names.

Motivating cases:

- `open FStar.Seq; open FStar.List.Tot` and then `length s` for `s : seq a`. ulib alone has
  ~492 `open`s, and `FStar.Seq.Base` and `FStar.List.Tot.Base` both export `length`,
  `index`, `mem`, `append`, `map`, `create`, `upd`, `equal`.
- `+` on `Prims.int`, `Prims.nat`, `FStar.UInt32.t`, `FStar.UInt64.t`, instead of today's
  `+^` workaround.

---

## 2. Design decisions

### 2.1 Conservative extension, not "unique match or error"

The proposal's literal rule — collect all matches, error unless unique — turns a large
amount of currently-working ulib/src/pulse/tests code into ambiguity errors, because
shadowing is relied on pervasively. `make ci` would not pass without a large fix-up
campaign.

Instead, **scope order is retained as the tie-breaker**:

1. Local binders / rec bindings win outright and are **never overloaded**.
2. Otherwise collect all candidates **in scope order** (innermost first). The order is the
   compatibility mechanism; it must not be discarded.
3. Eliminate candidates that are *definitely* type-incompatible (§2.4).
4. Exactly one survives → resolve to it.
5. Several survive → **pick the first**, i.e. exactly today's answer.
6. None survive → resolve to the first anyway, so the user sees exactly today's error.

Under this rule **no currently-working program changes meaning**: today's winner is always
candidate #1, and is only passed over when it is definitely ill-typed. Programs that used
to *fail* can start succeeding; nothing that succeeded can fail. This is what makes
"on by default" a realistic goal.

### 2.2 The fv keeps the scope-order winner; the qualifier carries only alternatives

The record-literal precedent puts a `__dummy__` lid in the head fv (ToSyntax.fst:1646),
meaningless until the typechecker rewrites it. That is tolerable for records, which occur
in exactly three syntactic positions (record literal head ToSyntax.fst:1645-1648, `Project`
head :1676-1690, `Pat_cons` :777-799). It is **not** tolerable for arbitrary names, which
can occur unapplied (`let g = f`), under `Tm_uinst`, in `Tm_ascribed`, in types, `val`s,
binder annotations, `requires`/`ensures`/`decreases`, attributes, `Tm_quoted`, `%splice`,
`Pat_dot_term`, and in Pulse source with its own desugaring hook. A single missed
resolution path becomes a crash, or a `__dummy__` lid serialized into a `.checked` file.

So instead:

```
| Unresolved_name of list fv   (* alternatives, in scope order; the primary is fv_name *)
```

The fv itself holds exactly what ToSyntax produces today. Consequences:

- Every subsystem that does not know about overloading — `Normalize`, NBE,
  `TypeChecker.Core`, extraction, reflection, printing, `.checked` serialization, Pulse —
  sees an ordinary fully-resolved fv and behaves exactly as today. The feature *degrades*
  to today's semantics rather than crashing.
- The conservative-extension property of §2.1 becomes structural rather than something the
  algorithm must remember to implement.
- It composes with the `--ext` gate: flag off ⇒ the list is never populated.
- Caveat: `fv_qual` is a single field, so a name whose primary already has a qualifier
  (`Data_ctor`, `Record_projector`) cannot also carry alternatives. Hence data
  constructors are deferred (§7.1).

### 2.3 Pluggable scoring; only the skeleton is shared

"Consolidate with `Unresolved_constructor`/`Unresolved_projector`" understates the gap.
**The record constructor case is not resolved by argument types at all.** Tracing it:
ToSyntax (:1634-1648) looks the record up by its **field-name set**
(`try_lookup_record_by_field_name_many`), storing the guess in `uc_typename` and the
source-written field names in `uc_fields`; field *values* are deliberately kept out of the
qualifier ("qualifiers intentionally are not meant to contain terms", ToSyntax.fst:1622-1629).
TcTerm (:1203-1214) then prefers a **type** signal, falling back to that guess;
`TcUtil.find_record_or_dc_from_head_fv` (TypeChecker.Util.fst:2502-2531) implements exactly
that.

| case | discriminating signal | arg types? | arity? |
|---|---|---|---|
| record literal `{f=v; ...}` | expected type, else `{e with}` base-term type, else **field-name set** | **no** | well-formedness check only (TcTerm.fst:1194-1198) |
| `Pat_cons` record pattern (TcTerm.fst:3453) | **scrutinee type** only | no args at all | no |
| projector `e.f` (TcTerm.fst:1267-1297) | type of the **first argument only**, else `try_lookup_dc_by_field_name` | one | no |
| general `f` (proposed) | arity + all argument types + expected type | yes | yes |

These are four different problems sharing a *shape*: speculate → score → pick → rebuild →
re-check. **Shared:** that skeleton plus the plumbing (error suppression during
speculation, `Rel` snapshot/rollback, memoisation, a uniform "candidates were …, argument
types were …" diagnostic). **Not shared:** the scoring, which must be pluggable with
per-case candidate generation and per-case discriminators. Applying a single
"best match over unrefined argument base types" to the record cases would be a *regression*
— it would throw away the field-name signal, the only signal available for a bare
`{ f = 0 }` with no expected type.

Therefore: do the skeleton refactor **first, as a pure no-behaviour-change commit** (p1),
verified by `make ci`. The record paths carry subtle behaviour
(`TcUtil.make_record_fields_in_order`, implicit-field wildcards at TcTerm.fst:1255-1257,
constructor parameter padding at :1263) that is easy to break.

### 2.4 The compatibility test must over-approximate

Step 3 must be an **over-approximation of compatibility**: eliminate only on *distinct
rigid head symbols*. A false-positive elimination is the only way this feature can break
working code.

`base(t)` = head symbol of `N.unfold_whnf' [Unascribe; Unmeta; Unrefine] env t`
(cf. TcTerm.fst:1286), classified as:

- **`Rigid l`** — head is an fvar `l` with no unfoldable definition. Compared by **head
  symbol only**: `list int` and `list bool` are indistinguishable. This keeps the test
  cheap, purely syntactic, and immune to uvars in type arguments, which is what makes it
  safe to run speculatively. `FStar.UInt32.t` is `new val t : eqtype`
  (FStar.UInt32.fsti:47) — abstract, hence rigid — which is precisely what lets `+` on
  `UInt32.t` be separated from `+` on `int`. **Do not unfold abstract types**, or `t`
  collapses to `Prims.int` and the operator overload dies.
- **`RigidType`** — head is `Tm_type`. Separates a type-valued candidate from a term-valued
  one at a type-annotation position. **Compare only "is a `Tm_type`", never the universe**,
  or universe polymorphism causes false eliminations. `eqtype` unrefines to `Type`, as
  intended.
- **`Unknown`** — uvar, bound/type variable, unresolved implicit, arrow, or the term failed
  to check. Arrows are deliberately `Unknown`: a candidate's formal may be a type
  abbreviation we chose not to unfold.

**`Unknown` never eliminates.** Elimination requires two distinct rigid heads.

Rejected alternatives: full `U.eq_tm` on the unrefined type (breaks the moment a uvar or
abbreviation appears); unifiability via `Rel.try_teq` (order-dependent, and speculative
matching would *solve* uvars as a side effect).

Consequences to document: a polymorphic formal (`id : #a:Type -> a -> a`) has a variable
base type, so it never eliminates and therefore simply loses to scope order — no
specificity order is needed. `int` and `nat` collapse under unrefinement, so there is
exactly one `+` covering both, and you cannot overload `nat` against `int`. An `int`
argument against a `nat` formal *looks* compatible and defers the failure to SMT, which is
the correct behaviour.

### 2.5 Argument types are frequently unknown, and that is fine

The projector case already shows the cost (TcTerm.fst:1281-1284): `clear_expected_typ`,
`tc_term env e`, **discard the guard**, then re-`tc_term` the whole application.
Generalized, that gives re-checking blowup on nested applications, leaked implicits from
uvars created in the throwaway pass, and bogus errors from a pass meant only to sniff a
type.

Crucially, arguments that *need* an expected type cannot be pre-checked at all: `f []`,
`f (fun x -> x + 1)`, `f None`, `f 0uy`, `f (Some x)`. Under `clear_expected_typ` these
yield uvars or outright fail. The `Unknown` outcome of §2.4 handles this: it neither
matches nor eliminates, and must never become a spurious ambiguity error.

Mitigations: only speculate when `|C| > 1`; stop as soon as `|C| = 1`; memoise; run under
`Errors.catch_errors` and a rolled-back `Rel` snapshot. The skeleton should *fix* the
guard-discarding bug rather than replicate it.

### 2.6 Arity is not a naive discriminator

F* is curried and implicit-heavy: `f x y` may be arity-2, or arity-1 returning a function,
or arity-4 with two implicits. Extracting the formals of a candidate requires
`N.unfold_whnf` on its type (it may be a type abbreviation, or a `Tot` of an arrow), then
keeping the explicit/implicit distinction, then walking into result `comp`s. "The number of
arguments" alone misfires on `#a:Type -> a -> a`, on effectful arrows, and on `let f = g`
aliases.

### 2.7 Types and terms are handled uniformly

Confirmed in the code, and it makes this cheaper rather than more expensive: ToSyntax has a
**single case** for both, `| Var l | Name l -> desugar_name mk setpos env true l`
(ToSyntax.fst:1031-1032), where `Var` is the term-level identifier and `Name` the
type-level one. Type-level applications are `Tm_app` and go through the same dispatcher.

Two consequences shape the design:

- **0-ary occurrences become the dominant case.** A type annotation `x:t` is a bare
  `Tm_fvar` with no application, handled by `tc_value` (TcTerm.fst:778-786, and the
  `Tm_uinst` case at :1824-1828) — *not* by the `Tm_app` dispatcher at :1047-1049. Both
  insertion points are required; for terms the app case dominates, for types the 0-ary one.
- **Type-level discrimination is intrinsically weak.** For `c a1..ak` at type level every
  `ai : Type`, so argument base types cannot separate two type constructors of equal arity.
  Arity and the expected type do what work there is; otherwise scope order. Document this
  so nobody expects `list` vs `set` to be separated by their element types.

### 2.8 Operators get no special treatment in resolution

Mangling is where operators legitimately differ; resolution must not be.

`compile_op` (Parser.AST.fst:370-411) builds `"op_" ^ String.concat "_" (map name_of_char chars)`,
and `op_as_term` (ToSyntax.fst:232-268) then does:

```
match desugar_name' ... env true (compile_op_lid arity (string_of_id op) ...) with
| Some t -> Some t          (* ordinary name resolution on the mangled name *)
| _ -> fallback ()          (* a hard-coded table: "+" -> Prims.op_Addition, ... *)
```

The mangled name and the name Prims actually defines agree only sometimes. Prims defines
`op_Addition, op_AmpAmp, op_BarBar, op_disEquality, op_Division, op_Equality,
op_Equals_Equals, op_GreaterThan, op_GreaterThanOrEqual, op_Hat, op_LessThan,
op_LessThanOrEqual, op_Minus, op_Modulus, op_Negation, op_Star, op_Subtraction`, whereas
`compile_op` produces `op_Plus, op_Slash, op_Percent, op_Equals, op_Less, op_Less_Equals,
op_Amp_Amp, op_Bar_Bar, op_Tilde, op_Less_Greater, ...`. So:

- `-` (`op_Minus`/`op_Subtraction`), `*` (`op_Star`), `^` (`op_Hat`), `==`
  (`op_Equals_Equals`) **resolve by ordinary name lookup**;
- `+`, `/`, `%`, `=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `~`, `<>` **only ever reach the
  hard-coded table**, because their mangled name is defined nowhere.

Because the table is a lookup-*failure* escape hatch, `Prims.op_Addition` is not a
candidate at all when any `op_Addition` is in scope. That is exactly why ulib cannot define
`+` on machine integers today and uses `+^` (FStar.UInt32.fsti:329): defining `op_Addition`
in `FStar.UInt32` would make `1 + 2` fail for every client that opens it.

**The only change needed: the mangling table contributes a candidate rather than acting as
an escape hatch.** `op_as_term` collects candidates for the mangled name in the ordinary
way and appends the `fallback ()` lid as the final, lowest-priority candidate; from there
the uniform rules apply.

- **No opt-in list and no exclusions.** `/\`, `==>`, `<<`, `~` are ordinary symbols; if
  something in scope defines their mangled name it participates, exactly as for any other
  name. (Earlier drafts proposed excluding the logical connectives; that was special-casing
  and is dropped.)
- `let ( + ) (a b : U32.t) = ...` binds `op_Plus` via `compile_op 0` (ToSyntax.fst:653, :837).
  A use site `x + y` then has candidates `[FStar.UInt32.op_Plus; Prims.op_Addition]`, and
  argument base types pick between them.
- Normalising `op_Plus` vs `Prims.op_Addition` is explicitly **out of scope** here (§7.2).
  But it matters *now*, because if the table stayed an escape hatch then `*` would be
  overloadable and `+` would not, for no reason a user could see.

### 2.9 Invariants

- **Never consults SMT.** Independent of uvar solving order, `--z3rlimit`, `--quake`.
  Otherwise proof fragility masquerades as name resolution.
- **Identical under `--lax` / `--admit_smt_queries` / `--proof_recovery` and full checking.**
  Dependencies are lax-checked before extraction; if lax mode resolved `f` differently,
  extraction would silently emit a different program than was verified. This is the most
  serious correctness hazard in the design.
- **No unresolved fv survives `tc_term`.** Add a defensive check. §2.2 makes a leak
  degrade rather than crash, but it should still be caught.
- Adding an overload to a module must not break distant clients — guaranteed by §2.1, since
  a new candidate can only ever be *added* after the existing winner.

---

## 3. The resolution rule (normative)

For an occurrence of an unqualified name `f` with candidates `C = [c0; …; cn]` in scope
order (`c0` = today's answer), `k` explicit arguments `a1..ak`, optional expected type `T`:

1. If `f` resolved to a local binder or rec binding, `C = [c0]`. **Locals are never
   overloaded.**
2. Dedupe `C` by fully-qualified lid — `FStar.Seq` `include`s `FStar.Seq.Base`, so one
   definition is reachable under several in-scope modules and those are not alternatives.
3. If `|C| = 1`, resolve to `c0` immediately, with no speculation and no cost. This must be
   the overwhelming common case.
4. Compute `formals(ci)` per §2.6. Eliminate `ci` if it cannot accept `k` explicit
   arguments (too few binders and the result is neither an arrow nor unknown).
5. For `j = 1..k` left to right, while `|C| > 1`: compute `base(aj)`; if `Unknown`, skip;
   otherwise eliminate every `ci` whose `j`-th explicit formal has a *rigid* base with a
   different head.
6. If `|C| > 1` and `T` is available, apply the same test to `T` against each candidate's
   result type after `k` applications.
7. Pick: `|C| = 1` → it. `|C| > 1` → **head of `C`** under `compat`, ambiguity error under
   `strict`. `|C| = 0` → `c0`, so the user sees exactly today's type error.

---

## 4. Phases

Tracked in SQL. Each is a separate commit and must leave `make -skj$(nproc) 3` green.

- **p0-option** — `--ext fstar:overload` = `off` | `compat` | `strict` via `Options.Ext`
  (cf. `FStarC.Plugins.fst:120`, `FStarC.Range.Ops.fst:156`), default `off`; plus a
  resolution-tracing debug flag following the `dbg_RFD` pattern (TcTerm.fst:1288).
- **p1-skeleton** — *no behaviour change.* New `FStarC.TypeChecker.Overload` with the
  shared skeleton of §2.3: speculative checking (error suppression + `Rel` snapshot/rollback
  + memoisation), `base_of_typ` (§2.4), and a uniform diagnostic printing every candidate
  with its fully-qualified name and type plus the inferred argument types. Rewrite the three
  existing paths onto it: TcTerm.fst:1184 (record literal), :1267 (projector), :3453 (record
  pattern). Gate: `make ci -j$(nproc)` clean, including `boot-diff`.
- **p2-syntax** — add `Unresolved_name of list fv` to `fv_qual` (Syntax.fsti:338-348),
  populated only when the primary's qual would be `None`. Update `Print.Ugly`, `Syntax.Hash`,
  `Syntax.Compress`, deep embeddings; check whether the `.checked` format version needs a bump.
- **p3-dsenv** — collecting variant of `try_lookup_id''`: stop at
  `Local_bindings`/`Rec_binding`; else accumulate across `Open_module` opens honouring
  `is_ident_allowed_by_restriction` and following `include` chains via
  `find_in_module_with_includes` (DsEnv.fst:392-429); plus `Top_level_defs` and
  `lookup_default_id`. Preserve scope order, dedupe by lid, run only when the option is on.
  Namespace-opens are correctly ignored already (DsEnv.fst:462-465 returns `Cont_ignore`).
  Must touch only the `Term_name` branch of `foundname` (§7.3). Add a debug assert that the
  head equals today's `try_lookup_lid` answer — the cheapest guard against violating §2.1.
- **p4-tosyntax** — attach alternatives in `desugar_name'` (ToSyntax.fst:215-226), covering
  `Var` and `Name` uniformly via the shared case at :1031-1032. In `op_as_term` (:232-268),
  append the `fallback ()` lid as the final candidate per §2.8.
- **p5-tctc** — resolution at both insertion points: the `Tm_app` dispatcher
  (TcTerm.fst:1047-1049, which returns `either` and falls through on `Inr`) and `tc_value`
  for 0-ary occurrences. The dispatcher matches `(SS.compress lhead).n`, which does **not**
  strip `Tm_uinst`, and ToSyntax *does* emit `Tm_uinst` for explicit `f u#0`
  (ToSyntax.fst:1067-1072, :1258-1264) — so handle `Tm_uinst({n=Tm_fvar fv}, us)` and rebuild
  it after picking. Strip the qualifier once resolved.
- **p6-tests** — `tests/overloading/` with `.expected` files: `Seq.length` vs
  `List.Tot.length`; expected-type and arity disambiguation; `+` on `UInt32.t` vs `int` vs
  `nat`; **type-level overloading** (0-ary `x:t`, and a type constructor separated by arity);
  locals shadow unconditionally; unknown-argument-type fallback vs `strict` error; `include`
  re-exports deduped; `open ... { ... }` restrictions; record/projector/pattern regressions
  from p1; effect-name resolution unchanged (§7.3); lax and non-lax resolve identically
  (compare extracted output); stability under `--quake`.
- **p7-measure** — `make ci -j$(nproc)` with the option `off` (must match master) and
  `strict`, collecting every ambiguity. That number answers whether unknown-argument-type
  sites should fall back to scope order or error.
- **p8-default** — flip the default only once p7 is clean. If `src/` itself starts *using*
  overloading, bump stage0 via `./.scripts/bump-stage0-from-stage1.sh` in a commit containing
  nothing else (CONTRIBUTING.md). Update `doc/` — user-visible language change.

---

## 5. Risks, ranked

1. **Cost on the common path** — collection runs at every identifier occurrence, and with
   types included that is now every type annotation too. p3 must short-circuit hard at 0 or 1
   candidate and memoise per `(scope_mods fingerprint, ident)`.
2. **Speculative re-typechecking blowup** on nested applications (§2.5).
3. **Lax/non-lax divergence** silently changing extracted code (§2.9).
4. **False-positive elimination** from over-eager delta-unfolding of abstract types (§2.4).
5. **IDE regression** — `DsEnv.resolve_to_fully_qualified_name` (DsEnv.fst:829) backs
   goto-def/hover and `--print_full_names`, and becomes ambiguous at desugaring time.
   Interactive mode (`src/interactive/`) would need to consult post-typechecking resolution.
6. **`boot-diff`** — the compiler must remain a fixed point, so any change to how `src/`
   itself resolves names shows up there.
7. **Typeclasses** — TC resolution is deferred to the end of the enclosing definition, while
   overload resolution wants argument types now. Under §2.4 a pending TC constraint yields
   `Unknown`, which never eliminates, so this degrades to scope order rather than deadlocking.

Not a risk: dependency analysis. `Parser.Dep` records deps from `open`/`include`/`friend`
(Dep.fst:1404-1444), so candidates from opened modules are already dependencies.

---

## 6. Resolved questions

- **Backwards compatibility** — conservative extension with scope-order tie-break (§2.1),
  so default-on is a realistic goal and `[@@overloadable]` is not needed.
- **Unknown argument type** — scope-order fallback or error is **decided empirically by p7**;
  land on `compat`.
- **Types and terms are handled uniformly** (§2.7). F* has no special distinction between
  types and terms; all names are handled the same way.
- **Operators are handled uniformly too** (§2.8). Mangling stays special; resolution does
  not. No opt-in list, no exclusions.
- **Effect names are out of scope** (§7.3).
- **Head-symbol equality only** (§2.4). `list int` and `list bool` are indistinguishable.
- **Data constructors are deferred**, not rejected (§7.1).

---

## 7. Deferred follow-ups

Each is independent; none requires rework of the phases above.

### 7.1 Data constructors overload uniformly

The target is for them to be handled the same way as everything else. The first cut leaves
them alone because `fv_qual` is a single field and constructors already occupy it with
`Data_ctor` (§2.2). Needs either a qualifier product or folding constructor resolution into
the existing `Unresolved_constructor` path. Once p1's skeleton exists this is a new scoring
plug-in rather than new machinery. It also subsumes pattern positions (`Pat_cons`), the
harder half.

### 7.2 Normalise the operator mangling table

Make `compile_op` and the Prims names agree: `op_Plus` vs `Prims.op_Addition`, `op_Amp_Amp`
vs `op_AmpAmp`, `op_Slash` vs `op_Division`, `op_Equals` vs `op_Equality`, `op_Less` vs
`op_LessThan`, `op_Tilde` vs `op_Negation`, `op_Less_Greater` vs `op_disEquality`. When this
lands, the appended fallback candidate from p4 becomes redundant and that special case
disappears entirely.

### 7.3 Effect names

`Tot`, `Lemma`, `ST` and effect abbreviations resolve through a separate path
(`Env.is_effect_name` at ToSyntax.fst:2195; `try_lookup_effect_name`, returning the
`Eff_name` branch of `foundname` rather than `Term_name`). That path is left exactly as it
is, and p6 includes a regression test that it is unchanged.

---

## 8. Progress

| phase | status | notes |
|---|---|---|
| p0-option | pending | |
| p1-skeleton | pending | |
| p2-syntax | pending | |
| p3-dsenv | pending | |
| p4-tosyntax | pending | |
| p5-tctc | pending | |
| p6-tests | pending | |
| p7-measure | pending | |
| p8-default | pending | |

---

## Appendix A: original proposal (verbatim)

> Let's implement support for type-based overloading resolution.
>
> Currently, a function symbol `f` is resolved in the desugaring phase purely by
> its name, checking for matching in the local environment and in any open
> top-level namespaces.
>
> Disambiguating names requires qualifying them with their explicit module name,
> which is inconvenient, or requires module designers to pick distinct names from
> other modules, which is also unpleasant & non-modular.
>
> F* supports some small amount of type-based disambiguation for names, but this
> is currently only limited to constructors and projectors.
>
> We should generalize this to all names.
>
> In the desugaring phase, when resolving a name `f`, we should find all possible
> name matches in scope and record them in an attribute/metadata associated with
> the name. If no names are found, then we should raise an unresolved name error,
> as we do now.
>
> Then, during typechecking, when `f` is used we should resolve the names by
> considering:
>
> * the application arity of the application site of `f`, e.g., it could be zero
>   if `f` is unapplied, `1, 2` etc. depending on the number of arguments.
>
> * for each argument, we should also record the types of those arguments
>
> * and, if available, the expected type from the context
>
> Based on this information, we should define a function to pick the best match
> from the candidate names and then use that as the resolutions of `f`. If there
> is no unique best match, we should raise an error saying the `f` could not be
> resolved.
>
> The main work then comes down to defining the best match function. Let's keep it
> simple:
>
> - We consider the unrefined base type of the each argument, e.g., if the
>   argument has type `x:nat{x > 17}` then the unrefined base type is `Prims.int`
>
> - We match the unrefined argument types against the unrefined types of the
>   formal parameters of `f`. If there is a unique match where the arguments base
>   type matches the formals' base type, then we have a resolution.
>
> - If the expected type of the context is available, then we can also use the
>   unrefined base type of the expected type against the base type resulting from
>   the `n`th application of `f`, where `n` is the arity of the application site.
>
> Consolidate the logic implementing this with the support for
> Unresolved_constructor & Unresolved_projector, so that we have a unified
> treatment of type-based overloading.
>
> Write a test suite to exercise the various cases, and then make sure we can pass
> a full clean `make ci -j$(nproc)` regression suite.

Deviations from the original, and why:

- **"error if no unique best match" → scope-order tie-break** (§2.1). The literal rule
  breaks a large amount of working code.
- **"consolidate with Unresolved_constructor/projector" → consolidate the *skeleton* only**
  (§2.3). The record cases discriminate by field names and scrutinee type, not argument
  types; a single scoring function would regress them.
- **"unresolved name error if none found" → unchanged behaviour** (§2.2). The fv keeps the
  scope-order winner, so a zero-candidate lookup produces exactly today's error.
- **Data constructors deferred** (§7.1), effect names out of scope (§7.3).
