# Project Custard

Custard is a new whole-program extraction pipeline for F*.  (It's what's under
the karamel in a creme brulee.)

The main goal is to support type-class monomorphization, so that we can use
type classes (e.g. for sorting algorithms) in Pulse while generating performant
code.  Monomorphization should also be opt-in for functions; also to support
higher-order combinators in Pulse.

There are several other shortcomings of the ML extraction that Custard will
address:
 - Aggressive type representation:
  - `type foo = | Foo of bar` should be a zero-cost newtype (equivalent to
    `type foo = bar`)
  - `type foo = { b: bar; p: prop }` should also be a newtype (erased fields
    like p should have no effect on the representation, and after removing `p`
    this is a single-field structure that should be a newtype).
  - `type foo = { a: prop; b: prop }` should be erased
 - On-demand compilation: Custard takes an entrypoint function as argument and
   only compiles its dependencies. (F* compiles everything, and that is both
   slow and can fail for non-compilable code)
 - repr/magic is built-in (and can be optimized away)

Non-goals:
 - Reusing existing ML extraction
 - ABI compatibility with existing ML extraction
 - Separate compilation
 - Generating multiple targets from the same IR
 - Pretty C code
 - Preserving location information
 - Preserving code structure (ANF is acceptable)

Diagram:

 All F* checked files --> monomorphized Custard IR --> Karamel
                                                   --> ML
                                                   --> C (directly)

---

## 0. Status and reading guide

This document is a design sketch, not a specification of shipped code.
Sections 1–3 describe the parts that are settled enough to implement;
sections 4–9 describe the surrounding machinery; section 11 lists the
decisions taken and the questions still open; section 12 is the design for
separate compilation, and section 13 the milestone breakdown.

Throughout, references to existing F* compiler code are given as
`src/<dir>/<Module>.fst:<line>` so the design can be checked against reality.
The relevant existing pipeline is:

| Concern | Existing code |
| --- | --- |
| ML IR | `src/extraction/FStarC.Extraction.ML.Syntax.fsti` |
| Term → ML | `src/extraction/FStarC.Extraction.ML.Term.fst` |
| Sigelt/module → ML | `src/extraction/FStarC.Extraction.ML.Modul.fst` |
| Extraction env | `src/extraction/FStarC.Extraction.ML.UEnv.fsti` |
| Unused type params | `src/extraction/FStarC.Extraction.ML.RemoveUnusedParameters.fst` |
| Krml backend | `src/extraction/FStarC.Extraction.Krml.fst` |
| Driver / `emit` | `src/fstar/FStarC.Universal.fst:304` |
| Checked-file loading | `src/fstar/FStarC.CheckedFiles.fsti:73` (`load_module_from_cache`) |
| Normalizer steps | `src/typechecker/FStarC.TypeChecker.Env.fsti:30` (`type step`) |

Custard lives in a new directory `src/custard/`, added to `src/fstar.include`,
with modules named `FStarC.Custard.*`.  It does not modify
`FStarC.Extraction.ML.*`; the two pipelines coexist and are selected by
`--codegen`.

---

## 1. Overall architecture

Custard is a *whole-program*, *demand-driven*, *monomorphizing* extractor.  It
is structured as a worklist algorithm over an explicit table of specializations
rather than as a per-module traversal.

```
  entrypoint lid(s)
        |
        v
  [ Driver ]  ---- on demand ---->  [ Checked-file loader ]  (CheckedFiles)
        |                                     |
        |                                     v
        |                            TcEnv with sigelts
        v
  [ Extraction loop ]  <---->  [ Normalizer ] (reify, delta, iota, primops)
        |     ^
        |     |  new specialization requests
        v     |
  [ Specialization table: (lid, mono-args) |-> fresh name + IR decl ]
        |
        v
  [ Post-passes: repr analysis, erasure, newtype collapse, DCE, ANF ]
        |
        +--> Krml AST  (.krml)
        +--> OCaml/ML AST (reuse ML.Code printer or a new one)
        +--> C directly
```

Key differences from the ML extraction:

1. **Demand-driven, not module-driven.**  The ML extractor is invoked once per
   module from `FStarC.Universal.fst:448` (`maybe_extract_mldefs`) and extracts
   every non-`noextract` sigelt.  Custard starts from an entrypoint and pulls.
   Nothing unreachable is ever looked at, so unextractable code (ghost-only
   modules, `assume val`s never called, code that would hit
   `err_cannot_extract_effect`) costs nothing.
2. **The unit of extraction is a specialization, not a definition.**  The
   result of extracting `bar` is not "the IR for `bar`" but "the IR for
   `bar@[string; foo_string]`".
3. **Types are computed, not translated.**  Because the program is
   monomorphic by the time we emit, the representation of every type is fully
   known and can be optimized (newtype collapse, erased-field removal, full
   erasure) with no ABI constraints.

### 1.1 Compilation phases

| # | Phase | Module | Input → Output |
| --- | --- | --- | --- |
| 0 | Option parsing, entrypoint resolution | `FStarC.Custard.Driver` | CLI → list of entrypoint lids |
| 1 | Dependency loading | `FStarC.Custard.Loader` | lids → `TcEnv.env` populated on demand |
| 2 | Extraction loop (monomorphization) | `FStarC.Custard.Extract` | env + worklist → raw IR program |
| 3 | Representation analysis | `FStarC.Custard.Repr` | IR types → layout table (erased / newtype / struct + field maps) |
| 3b | Effect classification | `FStarC.Custard.Effects` | comps → `eff`; runs with phase 2, constrains phase 4 (§7) |
| 4 | Simplification | `FStarC.Custard.Simplify` | IR → IR (coercion cancelling, DCE, ANF) |
| 5 | Emission | `FStarC.Custard.ToKrml` / `.ToML` / `.ToC` | IR → target |

Phases 2 and 3 are mutually recursive in practice (deciding whether an argument
is erased requires knowing the representation of its type, and computing the
representation of a type requires extracting it), so they share a fixpoint —
see §5.3.

---

## 2. IR

The IR is similar to the ML extraction IR (but kept separately so that we can
tweak it).  It's still a type-polymorphic typed lambda calculus.

Function-local recursive let-bindings are not supported (and need to be lifted
to the top-level).  This breaks the cycle between the declaration and term
types in the IR.

Discriminators are part of the IR, not just projectors.

### 2.1 Why still polymorphic?

Monomorphization is driven by *marked* binders (type-class dictionaries and
`[@@monomorphize]`), not by all type binders.  For the ML and Krml backends we
want to *keep* ordinary parametric polymorphism (`List.map` should stay one
function), and karamel already has its own monomorphizer for the cases that C
requires (`karamel/lib/Monomorphization.ml`, which interns
`lid × type-args ↦ mangled name`).  So the IR keeps `TVar`/`TApp` and a
type-scheme on each declaration.  A backend that wants full monomorphization
(direct-to-C) turns on `--custard_monomorphize_types`, which simply adds "all
type binders are marked" to the marking rules of §3.1; the IR type is unchanged
and the resulting program just happens to have no type variables.

A refinement worth having eventually, but not in v1: a type parameter that is
only ever used in erased positions does not need to be monomorphized even under
`--custard_monomorphize_types`, since it has no bearing on the generated code.
Detecting this needs a per-parameter "used relevantly?" analysis on top of the
layout table of §5, which is why it is deferred.

### 2.2 Sketch of the syntax

`src/custard/FStarC.Custard.Syntax.fsti`:

```fstar
type name = {
  ns:   list string;      // module path of the *original* definition
  id:   string;           // original identifier
  spec: option string;    // None for a definition that was never
                          // specialized; otherwise the suffix that
                          // distinguishes this specialization
}

type cty =
  | TVar     of ident
  | TArrow   of cty & eff & cty
  | TApp     of name & list cty      // named type, incl. arity-0
  | TTuple   of list cty
  | TUnit                            // the sole inhabited erased value
  | TExn                             // Prims.exn, the extensible variant (§8.5)
  | TAny                             // ML's MLTY_Top: representation unknown
```

Deliberate differences from `mlty`
(`src/extraction/FStarC.Extraction.ML.Syntax.fsti:58`):

- No separate `MLTY_Erased`.  Erasure is a *property computed by phase 3*
  (`Repr.layout_of : cty -> layout`, see §5), not a constructor.  Erased things
  are deleted outright by phase 4 rather than being turned into `unit` values
  that survive to the backend.  `TUnit` remains
  for the residual cases where a value must exist (e.g. an erased field of a
  multi-field record that we chose not to shrink, or a `unit`-returning
  effectful call).
- `TAny` replaces `MLTY_Top`.  Because the program is whole and monomorphic,
  `TAny` should be *rare*; it is an explicit signal that we lost information,
  and `--custard_warn_any` reports each occurrence.  This is a big usability
  win over the ML extraction, where `Obj.magic` sprinkles are invisible.

```fstar
type eff = E_Pure | E_Ghost | E_Impure   // cf. e_tag: E_PURE/E_ERASABLE/E_IMPURE

type constant = ...  // ints (with width), strings, chars, bool, unit

type pat =
  | PWild | PVar of ident | PConst of constant
  | PCtor of name & list pat
  | PRecord of name & list (string & pat)
  | PTuple of list pat
  | POr    of list pat

and expr = { e: expr'; ty: cty; eff: eff }   // every node carries its type

and expr' =
  | EConst  of constant
  | EVar    of ident
  | EQual   of name & list cty        // reference to a top-level decl, applied
                                      // to its remaining type arguments
  | ELet    of ident & cty & expr & expr        // non-recursive only
  | EApp    of expr & list expr
  | EFun    of list binder & expr
  | EMatch  of expr & list (pat & option expr & expr)
  | EIf     of expr & expr & expr
  | ESeq    of expr & expr
  | ECtor   of name & list expr
  | ETuple  of list expr
  | ERecord of name & list (string & expr)
  | EProj   of expr & name & string          // record/ctor field projection
  | EDiscrim of expr & name                  // NEW: `Foo? e`
  | ECast   of expr & cty                    // the *only* unsafe coercion node
  | EOp     of prim_op & list expr           // built-in ops (see §8)
  | EWhile  of expr & expr                   // statement-shaped, see §7.4
  | ERaise  of expr                          // §8.5; the value is an ECtor
  | ETry    of expr & list (pat & option expr & expr)
```

Notes:

- **Discriminators are IR nodes** (`EDiscrim`), so backends can compile
  `Foo? e` to a tag test instead of importing a generated function, and so the
  newtype collapse of §5 can rewrite `EDiscrim (e, Foo)` to `true` when `Foo`
  is the only constructor.  (In the ML extraction, discriminators and
  projectors are ordinary generated `Sig_let`s that get extracted as functions;
  see `Modul.fst`, and the `Projector`/`Discriminator` qualifier special-casing
  in `RegEmb.fst:826`.)
- **`ECast` replaces `MLE_Coerce` + `Obj.magic` + `FStar.Ghost.reveal`/`hide` +
  `admit`-style repr changes.**  It is `repr/magic built-in`.  Phase 4 cancels
  `ECast (ECast (e, t1), t2)` and drops `ECast (e, t)` when `e.ty` and `t`
  have the same layout — which, after newtype collapse, is very often the
  case.  This is the "can be optimized away" requirement.
- **No local `letrec`.**  `ELet` is non-recursive; local recursive functions
  and local closures that need to be recursive are lambda-lifted to top-level
  decls during phase 2 (which is easy: the extraction loop already creates
  top-level decls on demand, so lifting is just "request a specialization of a
  fresh name").  This is what breaks the `decl`/`expr` mutual recursion.

```fstar
type tydef =
  | TAbbrev of cty
  | TRecord of list (string & cty)
  | TVariant of list (name & list (string & cty))
  | TAbstract                         // assumed / externally realized

// F* has no inline record payloads, so each shape gets its own record type,
// with a per-constructor field prefix to keep field resolution unambiguous.
type dtype     = { dt_name: name; dt_params: list ident; dt_body: tydef;
                   dt_flags: list flag }
type dlet      = { dl_name: name; dl_typars: list ident; dl_binders: list binder;
                   dl_ret: cty; dl_eff: eff; dl_body: expr;
                   dl_flags: list flag }
type dexternal = { dx_name: name; dx_ty: cty; dx_flags: list flag }  // assume val
type dexn      = { de_name: name; de_args: list cty }

type decl =
  | DType     of dtype
  | DLet      of dlet
  | DExternal of dexternal
  | DExn      of dexn

type program = list decl    // topologically sorted; SCCs marked in `meta`
```

Recursion at the top level is expressed by a `Rec of list name` flag in the flags
(the SCC), rather than by a `let rec ... and ...` grouping, so that the
extraction loop can emit decls one at a time as it discovers them and fix up
SCCs at the end.

### 2.3 Names and mangling

A specialization is identified by a `spec_key`:

```fstar
type mono_arg =
  | MTy   of cty          // a monomorphized type argument
  | MTerm of expr         // a monomorphized term argument (dictionary,
                          // literal, closure) in normal form
type spec_key = lid & list (int & mono_arg)   // binder index -> argument
```

`spec_key`s are compared up to α-equivalence of the normalized arguments and
hash-consed in the specialization table.  The generated name is
`<Module>_<id>__<suffix>`, where the suffix is a readable reminder of what the
specialization was for — the head symbol of the first monomorphized argument
(`bar__string`) or a literal (`loop_unrolling__10`) — falling back to the
sequence number when there is nothing readable to say, and to
`<readable>_<n>` when two specializations would otherwise collide.  This
mirrors what karamel already does in `karamel/lib/Monomorphization.ml`.
Readability of these names is the *only* debugging aid we provide (locations
are an explicit non-goal, and no `spec_key ↦ name` side table is needed).

*Every* specialization carries a suffix, including one that turns out to be
the only one, and only a definition that was never specialized at all keeps
its bare name.  The alternative — numbering from zero and letting `__0` be
implicit — makes a name mean different things depending on how many siblings
happen to exist, so that adding a call site elsewhere in the program silently
renames a function.

---

## 3. Compilation

The top-level custard compiler takes a function, say `main`, as argument, and
then recursively traverses the monomorphized call graph.

    class foo (a: Type) = { frobnicate: a -> string }
    instance foo_string : foo string = { frobnicate = fun x -> x }
    let bar #a {| foo a |} (x: a) = frobnicate x
    let baz #a (x: a) {| foo a |} = bar x
    let main () = baz "frob"

Here, the type-class parameters `{| foo a |}` are monomorphized (no need for
extra annotations, we mark all TC parameters for monomorphization).  This
implies that their dependencies (in this case the `#a` binder is monomorphized
too) need to be monomorphized too.

We also add a `[@@@monomorphize]` attribute to mark other arguments for
monomorphization.

In the example, we traverse the following functions:
    - `main`
    - `baz string foo_string`
    - `bar string foo_string`
    - `Mkfoo.frobnicate string`

We should inline (trivial?) TC projectors automatically, so this example will
generate three functions (main and the two specializations for baz and bar).

Implementation-wise we should use the normalizer the reduce a reify of the
function (like the very first step the ML extraction does).

The extraction loop should happen in tandem with some light constant folding
and inlining (basically what the normalizer does).  The following example
should generate eleven functions (main + 10 specializations of
`loop_unrolling`):

    let rec loop_unrolling ([@@@monomorphize] n: nat) (f: unit -> Dv unit) : Dv unit =
        if n > 0 then (f (); loop_unrolling (n-1) f)
    let main = loop_unrolling 10 fun _ -> ()

(Different targets might require different defaults.  For example if we're
going to C directly we might want to monomorphize type arguments by default as
well.)

### 3.1 Which binders are monomorphized

Given the type of a definition `t = b_1 -> ... -> b_n -> C`, each binder `b_i`
is classified as `Mono` or `Poly` by the following rules, applied in order.
The classification is a function of the *definition*, computed once and cached.

1. **Erased** binders (`b_i`'s type is non-informative, see §5.1) are neither:
   they are deleted.
2. `b_i` is a **type-class dictionary** ⟹ `Mono`.
   Detection: the binder qualifier is `Some (Meta t)` where `t` is the fvar
   `FStar.Tactics.Typeclasses.tcresolve` (or `tcresolve_debug`), possibly
   eta-expanded.  This is exactly how `{| c |}` desugars — see
   `trans_bqual` in `src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:2483`, and the
   same test `U.is_fvar C.tcresolve_lid t` used by
   `src/typechecker/FStarC.TypeChecker.Rel.fst:5661` and the resugarer.
   Belt and braces: also treat a binder as a dictionary if its head type
   constructor carries the `FStar.Tactics.Typeclasses.tcclass` attribute
   (`Env.fv_has_attr env fv C.tcclass_lid`, cf.
   `src/typechecker/FStarC.TypeChecker.Quals.fst:364`), which catches
   dictionaries passed explicitly rather than through `{| |}`.
3. `b_i` carries the attribute `FStar.Attributes.monomorphize` ⟹ `Mono`.
   (New attribute, added to `ulib/FStar.Attributes.fsti`, with lid
   `Const.monomorphize_lid` in `src/parser/FStarC.Parser.Const.fst` next to the
   existing `tcclass_lid` &c at line 442.)  The whole definition may also carry
   `[@@monomorphize]`, meaning "all non-erased binders are `Mono`".
4. `b_i` is a **type binder** and `--custard_monomorphize_types` is on
   (default: on for the direct-C backend, off for ML/Krml) ⟹ `Mono`.
5. **Dependency closure**: if `b_j` is `Mono` and `b_i` is free in the type of
   `b_j`, then `b_i` becomes `Mono`.  Iterate to a fixpoint (it terminates: the
   set only grows and is bounded by `n`).  This is the rule that makes `#a` in
   `bar #a {| foo a |}` monomorphized without annotation.
6. A **type binder** still `Poly` after the fixpoint of rule 5 ⟹ deleted.
   Under the uniform compilation of types (§5.0) a type argument cannot change
   any layout, so it has no runtime content.  This has to be applied *after*
   the fixpoint, so that rule 5 still gets the chance to promote it to `Mono`.
7. Otherwise `Poly`.

**Opting a class out.**  Rule 2 says that a dictionary is known statically, and
for a type class that is what a type class is for.  But `tcclass` is also used
for things that are only *resolved* like classes and are otherwise perfectly
ordinary runtime values.  `FStarC.Syntax.Embeddings.Base.embedding` is the case
that forced the issue: an `embedding a` is a record of functions, built at run
time — `e_list e_sigelt` is a *call* — and passed around in lists and tables.
Made `Mono` it is unspecializable, and the extraction stops with error 363 at
the first binder whose embedding comes from a runtime parameter.

So a class may carry `[@@FStar.Attributes.custard_no_monomorphize]`, and a
binder whose head type constructor has it is `Poly`.  It beats the *inferred*
`Mono` of rules 2, 3 (the definition-level `[@@monomorphize]`) and 4, and loses
to a binder-level `[@@monomorphize]`, which is an explicit statement about that
one binder.  It is not applied inside rule 5's fixpoint: an opted-out binder
free in the type of a `Mono` binder is still promoted, because that promotion
is what makes the `Mono` binder's own type well-formed.

`Mono` binders are removed from the specialized definition's signature and
replaced by their concrete arguments in the body.  `Poly` binders remain.

**Custard never inspects the implicit/explicit qualifier of a binder.**
Whether an argument was written by the user or inferred by the elaborator says
nothing about whether it exists at runtime, and unlike the ML extraction
Custard has no interoperability obligation to reproduce the source arity.  (ML
extraction looks at the qualifier so that `val foo : 'a -> list 'a` becomes a
*unary* OCaml function while `val bar : Type -> Type -> nat` becomes a binary
one.  Custard emits its own top-level signatures and mangled names, so there is
nothing to match.)  Two dual rules replace the qualifier test:

- **At the value level**, a binder — and the corresponding argument at every
  call site — is deleted iff it holds no runtime value, i.e. iff it is a type
  binder or a `Dropped` (non-informative) binder.
- **At the type level**, an argument of a type constructor survives into the
  emitted `cty` iff its binder is a *type* binder.  A value index such as the
  `n` of `vec n` has no counterpart in the target's type language.

Signature and call sites derive their filtering from the same F* type, so they
agree without having to communicate.  Concretely, an implicit *value* binder
like the `#n` of `let addn (#n:int) (x:int) = n + x` is an ordinary parameter
that must be passed everywhere.

**The last-binder guard** (`Mono.keep_thunk`).  Two things can go wrong when a
binder is deleted, and both are about the *last* one.

Deleting *every* binder turns a definition from a function into a value, so its
body runs at module initialization instead of at the call, and a partial
application at some call site silently becomes a saturated one.  And a
unit-shaped binder in front of an impure codomain cannot be told apart, from
the type alone, from the thunk F\* writes exactly the same way: `unit -> ML a`
and `squash p -> ML a` are the same arrow, and only the programmer knows which
was meant.

So the last binder is retained when it would be deleted and either the
definition would otherwise become a value, or it is unit-shaped and the
codomain is impure.  It carries no information — its argument is `()` either
way — it just keeps the definition a function.  The first clause deliberately
does not test purity, even though running a pure body at initialization does
not change what the program computes, because F\*'s notion of purity is not
Custard's: a Pulse `fn f () : stt unit` is a `Tot` function returning an `stt`
*value*, and it is §7.2 that makes it an impure arrow.  Preserving the arity is
the answer that does not depend on which of the two notions is meant.

The guard is a property of a *signature*, so it does not apply to a
constructor, which is a value already — deleting all of a constructor's
arguments is precisely what a nullary constructor is.  Nor does it apply to the
binders that come from a definition's own lambdas rather than from its type
(`let boxed (n:int) : box int = fun () -> ...`), where there is no codomain to
consult; those keep the older, purely non-informative test
(`Mono.is_erased_binder`), which never touches a unit-shaped binder.

A known gap: a definition all of whose binders are `Mono` has the same problem,
and would need a thunk inserted at the definition and forced at each call site;
v1 does not do this.

The classification is *not* affected by whether the argument at a call site
happens to be a literal: `f 3` where `n` is `Poly` does not specialize.  We
want specialization to be predictable and declared, not accidental.

### 3.2 What a `Mono` argument must look like at a call site

Two things can go wrong at a call site, and v1 rejects both with a good error
rather than trying to be clever.

**(a) Partial application.**  If `g` has a `Mono` binder at index `i` and a use
of `g` supplies fewer than `i+1` arguments, we cannot specialize.  *v1 rejects*
with a message naming the definition, the binder, and the request chain that
reached it.  Eta-expansion is the obvious fix and is easy in the fully-applied-
after-eta case, but it is not worth doing until (b) is solved, because the two
interact: eta-expanding introduces a fresh local binder that then has to be
passed to a `Mono` position, which is exactly case (b).

**(b) A `Poly` argument flowing into a `Mono` position.**

```fstar
let use  #a {| foo a |} (x:a) = frobnicate x
let wrap #b (y:b) = use y            // `b` and the dictionary are Poly in wrap
```

Specializing `use` requires knowing `b` and the dictionary, but inside `wrap`
they are runtime-opaque parameters.  Note this does *not* happen for the common
type-class case, because a caller's dictionary binder is itself `Mono` (rule 2)
and hence already substituted by a concrete value before we look at the body —
the situation above only arises when the caller's binder was classified `Poly`.

Options:

1. **Reject** (v1).  Error: "`wrap`'s parameter `b` is passed to `use`'s
   monomorphized parameter `a`; mark `b` with `[@@monomorphize]`."  Predictable,
   and the fix is one annotation.
2. **Infer and promote** (likely v2).  Detecting this is a backwards dataflow
   problem over the call graph: if a `Poly` binder of `f` flows into a `Mono`
   binder of `g`, promote it to `Mono` and re-specialize `f`.  Because Custard
   is demand-driven the call graph is not known up front, so the natural
   implementation is *retry with promotion*: when the extraction loop hits this
   situation it records the promotion, discards the in-progress specialization
   of `f`, and re-requests it.  The promotion set only grows and is bounded by
   the number of binders, so it terminates; the cost is re-work, bounded by the
   number of promotions.
3. **Fall back to a generic (dictionary-passing) version of `g`.**  Rejected:
   it silently reintroduces the indirect calls that Custard exists to remove,
   and the performance cliff would be invisible.

Option 2 is compatible with option 1 (it just turns some errors into successes),
so v1 shipping the error is not a design commitment.

**What is *not* a problem.**  `Mono`/`Poly` is a property of a function
*parameter*, not of a value or a type, so the following are all fine:

- **Passing a `Mono` argument to a `Poly` parameter.**  Always legal — the
  callee simply doesn't specialize on it.  `Mono` is a demand, not a taint.
- **Computing a `Mono` argument from another `Mono` argument.**  If `d : list
  (foo a)` is a `Mono` parameter, then `List.hd d` is known at specialization
  time, so passing it to another function's `Mono` parameter is fine: the
  normalizer reduces it to a concrete dictionary before we intern the key.
  Anything projected, matched, or computed out of a `Mono` value is itself
  known at specialization time.

- **Naming a `Mono` argument with a local `let`.**  `let d = { cmp = f } in
  sort #a #d` is the same call as `sort #a #({ cmp = f })`, and is judged the
  same way: keys are computed with local `let`-bound variables replaced by
  what they are bound to, to a fixpoint.  This is not something the normalizer
  can do for us — by the time an argument is inspected it is a bare variable,
  the `let` that binds it is somewhere else, and `custard_norm_steps` carries
  `PureSubtermsWithinComputations` *precisely* so that pure `let`s are not
  substituted into the body, which is what keeps sharing and evaluation order
  intact in the emitted code.  So the unfolding is separate and one-directional:
  it happens on the way to the key and to the value substituted into the body,
  and never to the body itself.  Only pure definitions are unfolded; an
  effectful one is already evaluated by the `let` that stays behind, and baking
  it into a specialization as well would run it twice.

  This is what makes a dictionary *assembled on the fly* specializable, which
  is how `FStarC.Class.Ord.sort_by` is written and, by the measurement in
  §12.8 item 5, not a rare shape.

The *only* bad case is the one above: a value that exists only at runtime
reaching a `Mono` parameter.  The interesting instance of it is storing a
dictionary in a runtime data structure — a `ref (foo a)`, a dictionary read out
of a `Poly` list, a dictionary returned from a branch — and then trying to call
a method on it.  Supporting that would mean falling back to real
dictionary-passing for those call sites, which is a genuine performance cliff
and therefore must be **manual opt-in**, not inference.  Out of scope for v1;
v1 rejects, per option 1.

### 3.2c Arguments that are *partly* runtime: hole abstraction

Case (b) above is stated as though an argument were either wholly known at
specialization time or wholly unknown.  Real code produces a third shape far
more often than either: an argument whose *structure* is static and some of
whose *leaves* are runtime values.  The case that forced this was
`FStarC.Syntax.Embeddings.Base`:

```fstar
let embed_simple (#a:Type) {| e : embedding a |} (x:a) = ...
// at a use site, with [ta] an ordinary runtime value:
let emb = set_type ta e_any in
... e_sealed emb ...
```

`emb` looks unused, but F\* selects it as a *local instance*, so the dictionary
`e_sealed (set_type ta e_any)` is what reaches a `Mono` binder.  Every method in
it is statically known; only `ta` is not.  Rejecting the call throws away all
of the former because of a little of the latter, and no annotation can fix it —
`ta` is an honest runtime value, so promoting a binder to `Mono` (option 2)
does not apply either.

So Custard specializes on the argument's **skeleton** and passes its runtime
leaves as ordinary extra parameters.  Concretely, for a call whose `Mono`
arguments are `w1..wk`:

1. Collect the free names of the normalized `w1..wk`.  These are the *holes*.
   They are free names of an already-normalized term, so they are leaves:
   nothing more can be learned about them.  Abstracting maximal
   runtime-dependent *subterms* instead would just degenerate into ordinary
   dictionary passing.
2. Replace each `wj` by `fun v1..vn -> wj`, over the *same* list of holes for
   every argument, so that a value occurring in two arguments stays one
   parameter.
3. Key on those abstractions.  Nothing else is needed to make the key
   canonical: the key printer already prints binders by sort and bound
   variables by de Bruijn index, so alpha-equivalent skeletons print
   identically and share a specialization.
4. Emit the specialization with the hole binders *prepended* to its own, and
   pass the holes at the call site in the same order.

The specialization's signature is therefore `holes ++ poly`, and holes are
ordered by their de Bruijn index so that the order cannot depend on the order
the arguments happened to be visited in.

They go first because neither end of a call's spine is otherwise stable.  A
definition whose result type is an abbreviation hiding an arrow --
`f_term : {| lvm m |} -> endo m term`, where `endo m a = a -> ML (m a)` -- has
fewer binders in its type than a saturated call has arguments, so holes
appended to the spine would land *after* the arguments the body's own lambdas
bind.  A use that supplies fewer arguments than there are `Poly` binders --
`map_optM f_aqual`, where `f_aqual`'s own argument is the one `map_optM` will
supply -- would place them too early.  Only the front of the spine is the same
position under both.

Specialization does not take the definition apart to substitute; it applies
the definition to a spine and re-abstracts over what is left, which copes
uniformly with definitions that are eta-short, that have more binders than
their type shows, or that are not lambdas at all.  That is eta-expansion, and
so the spine stops at the definition's own lambdas unless the definition is a
value: a definition that *computes* before returning a function --- allocating
a memo table, say --- would otherwise compute again on every call.  See
§13.5.

The number of holes is part of the key (`sk_holes`), because the abstraction
step is not injective on terms alone: an argument genuinely written as
`fun (x:int) -> x` and an argument `x` with one `int` hole abstracted produce
the *same term* and differ only in arity.

This composes.  If a specialized callee passes one of its own hole parameters
to a further `Mono` binder, that becomes a hole there too, and the requirement
propagates outward until it reaches a call site where the value is concrete.

It also subsumes a case §3.2 never claimed to handle.  A closure argument
`twice (fun y -> y + k)` has static structure and one runtime leaf `k`, so it
specializes: the closure is inlined into the specialization and `k` is passed
as an `int`.  That is defunctionalization, falling out of the same mechanism —
compare §3.2's "function arguments" discussion, which anticipated needing an
explicit closure-conversion pass to get here.

**Two things are still rejected**, and deliberately.

- *A hole whose sort is a type.*  Types are erased under uniform compilation
  (§5.0), so there would be nothing to pass at runtime.  This stays the case
  (b) rejection it has always been, and option 2's promotion is the fix.
- *An argument that is nothing but a hole* — a bare variable.  Here the
  skeleton is the identity function, so nothing is specialized: the value is
  simply passed at runtime.  That is not unsound, it is **dictionary
  passing**, and it is gated for the reason §3.2 rejected option 3 —
  it reintroduces the indirect calls monomorphization exists to remove, and
  doing it silently would make the performance cliff invisible.  §3.2c widens
  what may be specialized; the gate is a policy about the degenerate end of
  the same mechanism, not a limit of it.

  This is worth stating plainly, because it took a while to see: hole
  abstraction and dictionary passing are not two mechanisms but one, and the
  skeleton is the dial between them.

  ```
  skeleton fully static ─────────────── skeleton = identity
  (pure monomorphization)      (pure dictionary passing)
        render p_int      render (set_tag n p_int)      render d
  ```

  Turning the gate off is therefore a policy change, not a new pass: the
  machinery that would pass `d` at runtime is the machinery that already
  passes `n`.  §3.2c1 opens it.

Two situations produce a bare variable, and Custard distinguishes them
because the *advice* differs even though the mechanism does not.  If it is a
**runtime parameter**, the fix is local and cheap: mark it
`[@@monomorphize]` in the caller, or drop the annotation on the callee's
binder.  If it is the result of an **effectful** `let` — which §3.2b's
`let`-unfolding deliberately leaves in place — then no annotation can help,
because the computation runs when the program runs and the value is never
known earlier.  Opting in to dictionary passing is the only route.

Note the effectfulness itself is *not* the obstacle, and an early draft of
this section had that wrong.  A hole is a free **name**, so it is always an
already-evaluated value; a computation can never become a hole, only its
result can.  The `let` stays exactly where it was written, runs exactly once,
and its result is passed like any other hole — so an effectfully-obtained
leaf specializes as happily as a pure one, and reaches the *same*
specialization as a pure caller does (`tests/custard/MonoHoles.fst`,
`from_ref`).  The obstacle is only that in these particular cases the
effectful result is the *whole* argument.

The motivating case is `FStarC.Syntax.VisitM`.  `tie_bu` builds a *recursive*
`lvm m` instance — each method has to visit subterms with the dictionary
being defined — and since F\* has no recursive value bindings, it ties the
knot through a `ref`:

```fstar
let r : ref (lvm m) = mk_ref (novfs #m #md) in
r := { lvm_monad = (!r).lvm_monad;
       f_term = (fun x -> f_term #_ #d <<| on_sub_term #_ #!r x); … };
!r
```

Every `#!r` passes a dereference into `on_sub_*`'s `{| lvm m |}` binder, so
every one of them is an identity skeleton.  Restructuring the knot as
mutually recursive functions removes the `ref`, and was measured to cost
nothing (+0.5% minor allocation, *less* major-heap traffic, wall time within
noise, because the per-node records die in the minor heap where the `ref` and
its record were promoted).  But it does not help: the replacement `bu_dict`
is still `ML`, so the argument is still the result of a computation rather
than a value, and there is no termination argument that would make it `Tot`.
A recursive, effectfully-tied dictionary is not something specialization can
reach by any restructuring of the source, and it should not be — it wants the
identity skeleton, which is to say it wants dictionary passing.  §3.2c1 is
how it asks; `tie_bu` now carries seven `dyn`s and `VisitM` extracts.

#### 3.2c1 `dyn`: asking for the identity skeleton

The opt-in is a marker applied to the **argument at the call site**, not a
qualifier on the callee's binder, because that is where the knowledge lives.
A binder like `on_sub_term`'s `{| lvm m |}` is worth specializing at almost
every call site; it is one caller, `tie_bu`, that cannot supply a static
value.  Marking the binder would pessimize all the others.  This is the same
reason, and the same shape, as Rust's `dyn`:

```fstar
val dyn (#a:Type) (x:a) : Pure a (requires True) (ensures fun r -> r == x)
```

`FStar.Custard.dyn` is the identity, and it is the identity in the sense that
matters twice over.  For the *program* it disappears: `Custard.Builtins` maps
it to a `Rule_prim` that compiles to its argument, so nothing survives into
the emitted code.  For a *proof* it is transparent, because the postcondition
`r == x` is in the specification.

What it is not transparent to is the normalizer, and that is the whole trick.
An ordinary identity function would be unfolded away while computing the
specialization key (`key_norm_steps`), leaving behind the bare variable it
was wrapping and the rejection that variable triggers.  So `dyn` carries an
attribute, `FStar.Custard.no_specialize`, that Custard names in a
`DontUnfoldAttr` step in every reduction it performs.

Given that, **nothing else in the pipeline changes**, which is the payoff of
the "one mechanism" framing above.  `dyn d` is not a `Tm_name`, so the gate
does not fire.  `d` is free in it, so `d` becomes an ordinary hole.  The
argument abstracts to `fun h -> dyn h` — the identity skeleton, literally —
and `d` is passed as a hole parameter.  Method projections `(dyn h).f_term`
stay unreduced for the same reason, and become real field accesses: dictionary
passing, assembled entirely out of §3.2c's existing parts.

`tests/custard/MonoDyn.fst` shows both ends of the dial reached from the same
callee:

```fstar
let render (#a:Type) {| printable a |} (x:a) : string = pr x

let from_ref (b:bool) (x:int) : ML string =
  let r = alloc p_int in
  if b then r := p_bool;
  let d = !r in
  render #int #(dyn d) x          (* identity skeleton *)

let static (x:int) : string = render #int #p_int x   (* fully specialized *)
```

emitting

```ocaml
let monoDyn_render__0 (x : Prims.int) : ((Prims.int -> string) -> string) = …
let monoDyn_render__int (x : Prims.int) : string = …
```

One wart is worth knowing about: **`dyn` must wrap a pure term.**  F\*'s ANF
phase lifts a whole effectful argument into a fresh `let`, marker and all, so
`render #int #(dyn !r) x` becomes `let uu___ = dyn !r in render #int #uu___ x`
and the marker is buried where Custard cannot see it.  Binding the dereference
first, as above, is enough.  A friendlier diagnostic here — recognising a
`dyn` at the head of an effectful `let`-definition and accepting it — is
possible but not yet implemented.

`dyn` is also no help for a *type* argument: under uniform compilation (§5.0)
there is no runtime value to pass, so the case (b) rejection above stands and
only option 2's promotion reaches it.  The diagnostic checks the sort of the
variable and only suggests `dyn` where it could actually work.

### 3.3 The extraction loop

State:

```fstar
type st = {
  env:      TcEnv.env;                       // grows as modules are loaded
  table:    hashtable spec_key name;         // interning
  emitted:  hashtable name decl;
  worklist: list (spec_key & name);
  fuel:     int;                             // see 3.6
}
```

`request : spec_key -> ST name` interns the key; if new, allocates a name,
pushes onto the worklist, and returns.  `run` pops until empty.

Processing one item `(lid, margs) ↦ nm`:

1. **Look up the definition.**  `Env.lookup_definition [Unfold delta_constant]
   env lid` (`src/typechecker/FStarC.TypeChecker.Env.fsti:462`) gives
   `(univs, body)`; `Env.lookup_qname` gives the sigelt, its qualifiers, and
   its attributes.  If the module isn't loaded yet, the loader (§4) loads it
   first.  If there is no definition (`assume val`, `Sig_declare_typ`), we emit
   a `DExternal` and consult the custom-rule table (§8).
2. **Reify and normalize.**  Substitute the `margs` for the `Mono` binders,
   then normalize.  Following the ML extraction (`Term.fst:639`,
   `Term.fst:1981`) the step list is:

   ```fstar
   let custard_norm_steps = [
     Env.AllowUnboundUniverses; Env.EraseUniverses;
     Env.Beta; Env.Iota; Env.Zeta;         // NB: unlike ML extraction we do
                                           // NOT Exclude Zeta at this point;
                                           // see 3.6 on fuel
     Env.Primops;                          // constant folding
     Env.Eager_unfolding; Env.Inlining;    // inline_for_extraction, unfold
     Env.PureSubtermsWithinComputations;
     Env.Reify;                            // reify effectful definitions
     Env.Unascribe; Env.Unmeta;
     Env.ForExtraction;
     Env.UnfoldAttr [Const.tcnorm_attr;     // force TC dictionary resolution
                     Const.tcmethod_lid];  // inline class method accessors
     Env.ReduceProjections;                // <-- collapses Mkfoo?.frobnicate d
   ]
   ```

   `ReduceProjections` plus `UnfoldAttr [tcnorm_attr; tcmethod_lid]` is what
   "inlines trivial TC projectors automatically": once the dictionary argument is a concrete
   `Mkfoo x y z` value, `Mkfoo?.frobnicate (Mkfoo f)` iota-reduces to `f`, so
   no method-projector functions survive into the IR at all.  The `solve`
   helper in `ulib/FStar.Tactics.Typeclasses.fsti:61` is already
   `[@@tcnorm] unfold`, so it reduces for free.

   Effects go through `TcUtil.effect_extraction_mode` exactly as
   `Term.maybe_reify_comp` does (`Term.fst:654`): `Extract_reify` reifies and
   renormalizes, `Extract_primitive` is handled by the effect rules of §7.2,
   and `Extract_none` is a hard error — but now only for definitions that are
   actually reachable, which is the point of on-demand compilation.
3. **Translate the normal form** to `expr`, requesting specializations as we
   go.  For an application head `EQual (g, _)` whose definition has `Mono`
   binders, we split the arguments, normalize the `Mono` ones to a canonical
   normal form, and `request (g, margs')`.  The two failure modes — partial
   application, and a `Poly` argument in a `Mono` position — are rejected here
   with the diagnostics of §3.2.
4. **Lambda-lift** local recursive functions and emit them as extra decls.
5. **Emit** the `DLet` and record it.

Types are handled by the same loop: `TApp (ind, args)` requests a
specialization of the inductive, which recursively requests specializations of
its constructor argument types.  This is where the `type foo = | Foo of bar`
newtype question gets answered (§5.2).

### 3.4 Worked example

For the type-class example above, the loop runs:

| Step | Request | Normal form of body | Emits |
| --- | --- | --- | --- |
| 1 | `main, []` | `baz string foo_string "frob"` | `main` |
| 2 | `baz, [0↦MTy string; 2↦MTerm foo_string]` | `bar "frob"` after substitution | `baz__0` |
| 3 | `bar, [0↦MTy string; 1↦MTerm foo_string]` | `Mkfoo?.frobnicate (Mkfoo (fun x -> x)) x` → `x` | `bar__0` |

Note `Mkfoo?.frobnicate` is *never* requested when it is applied to exactly the
dictionary: it is reduced away in step 3 by `ReduceProjections`.  When the
method is applied to further arguments (`Mkfoo?.frobnicate d x`, which is the
usual shape, because a method's result type is a function) the normalizer's
strict-projector check declines to fire, and the projector is instead requested
and specialized on `d` -- which reduces its body to the method implementation,
so the emitted code is correct but goes through one extra wrapper per method
call.  Collapsing those wrappers is the job of the inlining pass of section 6.  The draft says this example generates three functions;
that is what falls out.  The `foo` class type itself is also never emitted,
because no residual value of type `foo string` remains — dead-type elimination
in phase 4 removes it.

For `loop_unrolling`, binder 0 (`n`) is `Mono` by rule 3, binder 1 (`f`) is
`Poly`.  Requests are `loop_unrolling@10`, `@9`, … `@0`; the body of `@0`
normalizes to `()` since `Primops` folds `0 > 0` and `Iota` picks the branch.
Eleven decls, as the draft says.  Note that the recursive call is only
discovered *after* normalization of the body, which is why `Zeta` must be
handled carefully: we want to unfold `let rec` *definitions* on demand via the
worklist, not have the normalizer unroll them internally.  See §3.6.

### 3.5 Interaction with `Poly` arguments at specialization sites

`request` keys on the `Mono` arguments only.  Two call sites
`bar #string dict f` and `bar #string dict g` share the specialization
`bar__0` and pass `f`/`g` as ordinary arguments.  This keeps code size linear
in the number of distinct dictionary/type instantiations rather than in the
number of call sites.

### 3.6 Termination and fuel

Monomorphization of term arguments is not terminating in general
(`let rec f ([@@monomorphize] n:nat) = f (n+1)`), and even type
monomorphization diverges for non-uniform recursion
(`type t a = | C of t (list a)`).  Custard therefore:

- normalizes `Mono` arguments to a canonical form before interning, so that
  syntactically different but convertible arguments share a specialization;
- keeps a per-`lid` specialization counter, bounded by
  `--custard_max_specializations` (default 1000);
- keeps a global bound `--custard_fuel`;
- on exhaustion, reports the *chain* of specialization requests that led there
  (a `spec_key` provenance list), which is the only debuggable way to present
  this failure.

There is no attempt at a clever termination check.  Recursion through a `Mono`
binder is a user error and the diagnostic is what matters.

The one real requirement is that divergence be detected *quickly*: a runaway
specialization must not spend seconds normalizing each body before being cut
off.  So the counters are checked at `request` time — before the definition is
looked up and before its body is normalized — and the only work done per
diverging step is normalizing the `Mono` arguments to their canonical form.
With the default bounds a diverging program should fail in well under a second.

#### Bounding normalization itself

The counters above bound the number of specializations.  Nothing they do
bounds the work inside *one* of them, and normalization is not guaranteed to
terminate either: `Cfg.default_steps` sets `zeta = true` — so leaving `Zeta`
out of a step list does not disable it, a step list only ever adds — and
`Unfolding.should_unfold` will then unfold a recursive definition without
bound.  Custard is unusually exposed to this because it reduces terms nobody
wrote for it: a key has to be a normal form, so `key_norm_steps` is the most
aggressive reduction in the pipeline and it is applied to whatever value
happens to reach a `Mono` binder.

So every normalization Custard performs runs under `--custard_norm_budget`
(default 10,000,000 reduction steps), implemented as
`Normalize.with_budget`, which charges one step per call to `norm` — the
reduction machine's single entry point — and raises `Budget_exceeded` when the
count runs out.  Custard turns that into a fatal error naming what it was
normalizing and the request chain that reached it.

Two choices worth recording.  It is a **step count, not a time limit**,
because a compiler that fails should fail identically on every machine and
every run.  And the budget is *per normalization*, not per run, because the
question it answers is "is this one term diverging?", which is what the
diagnostic needs to name.

The default has room: extracting `FStarC.Syntax.Print.term_to_string` needs
under 10,000 steps for its largest single normalization, three orders of
magnitude below the default, so hitting the budget means something is wrong
rather than merely large.  `tests/custard/NormBudget.fst` pins the behaviour
with a definition that is `Tot` for the typechecker and divergent for the
normalizer; without the budget it hangs, with it it fails in three seconds.

### 3.7 Canonicalizing `Mono` arguments for interning

Two call sites should share a specialization when their `Mono` arguments are
"the same", and the definition of "the same" is a tuning knob: too weak and we
emit duplicate specializations (code bloat, and `loop_unrolling` never
terminates because `n-1` never becomes a literal); too strong and canonicalizing
the key costs more than the extraction.

This cannot be settled on paper — it needs measurement on real Pulse/HACL* code.
The plan is to **start minimal and widen empirically**:

| Iteration | Steps used to canonicalize a `Mono` argument |
| --- | --- |
| start | `Beta`, `Iota`, `Unascribe` (+ `EraseUniverses`, `AllowUnboundUniverses` as hygiene) |
| almost certainly needed | `+ Primops` — `loop_unrolling (n-1)` has to fold `10-1` to the literal `9`, or every recursive call produces a fresh key and we just burn fuel |
| if needed | `+ Delta`/`Eager_unfolding` for dictionaries hidden behind abbreviations, `+ Zeta` for `let`-bound dictionaries |

Note this step list is deliberately *much* smaller than the one used to
normalize a definition's body (§3.3): the body needs full reduction to expose
the call graph, whereas the key only needs enough reduction to make equal things
syntactically equal.  Keys are compared up to α-equivalence and hash-consed
(§2.3).

A useful diagnostic while tuning: `--custard_dump_specializations` listing
`lid ↦ number of specializations`, which makes both failure modes (bloat, and
fuel exhaustion) immediately visible.

#### The key is not what gets substituted

The canonical form computed here is the specialization's *identity*.  It is
**not** the term that gets substituted into the body, and conflating the two
is a trap worth spelling out.

The key steps include `Primops` and `UnfoldUntil delta_constant`, i.e. they
unfold everything and fold arithmetic.  That is exactly right for deciding
"are these two dictionaries the same dictionary?", and exactly wrong as the
argument to substitute, because it *runs the program at extraction time*.
The EverParse-style combinator of §3.9 makes this vivid: substituting the
fully normalized parser bundle folds the offset arithmetic `4 + 8`, which
forces every sub-parser to reduce to a concrete `Some (n, _)`, which lets
`Iota` collapse every `match` — and the whole grammar arrives inlined into
its root as straight-line code.  Its serializer, which contains neither
arithmetic nor a `match`, escaped untouched, which is what made the asymmetry
noticeable.

So the substituted form uses a *second*, weaker step list:

```
subst_norm_steps = Weak :: HNF :: key_norm_steps
```

`Weak` and `HNF` stop reduction at the head constructor with the field bodies
as written, so a sub-combinator stays a *call* rather than being evaluated.
If weak reduction leaves free names behind — it can, when the argument is not
a closed value — we fall back to the fully normalized term, which is always
sound, just less structured.

#### Printing the key

Keys are interned as strings, so the function that turns a canonicalized
`Mono` argument into text is load-bearing: it decides which call sites share
code.  It must therefore be injective up to the equivalence we intend, and
must depend on nothing but the term.

`show` is neither, and it is worth recording what went wrong, because the
symptom is a silent miscompilation rather than an error.  `Print.term_to_string`
resugars unless `--ugly`, and the ugly printer prints an `fv` by its **last
identifier alone** (`Syntax.fst:629`, `sli`).  So under `--ugly`, `A.tweak` and
`B.tweak` are one key.  `tests/custard/KeyNames.fst` is exactly that program —
two `assume val tweak`s in different modules, both passed to one
`[@@@monomorphize]` binder — and it used to emit a single specialization and
print `abab` instead of `abAB`.  Delta-unfolding in `key_norm_steps` masks this
whenever the argument reduces to a structure whose *contents* differ, which is
why type classes never showed it; what defeats the mask is an argument that
keeps an `fv` which does not unfold, such as an `assume val`, a
`[@@custard_extern]`, or an abstract type constructor.

`Extract.key_of_term` is a printer written for this one job: every `fv` and
effect name fully qualified, universes erased (matching `EraseUniverses`),
bound variables printed as their de Bruijn index and binders as their sort
alone — so the key is α-canonical for free, since terms are locally nameless
and are never opened — integer constants printed with their width and
signedness, and ranges, attributes, qualifiers and `ppname`s dropped as
non-semantic.  It is independent of every printing option; `KeyNames` runs
with `--ugly` on for precisely that reason.

The same string is what §12.2 stores in a unit interface, so it has to mean
the same thing in the next process as in this one.  The one construct that
cannot: a `Tm_name`, which is a variable bound *outside* the argument and so
has nothing canonical about it but a gensym index.  Such a key is fine within
a run and not portable across one; if separately compiled units ever need to
export such a specialization, that is the thing to fix.

### 3.8 Function-valued `Mono` arguments (deferred to v2)

Marking a *function* parameter `[@@monomorphize]` is genuinely harder than
marking a type or a dictionary, because the argument closure may capture the
caller's `Poly` variables, so it is not a closed term that can be substituted
and interned.

The intended v2 design is *ad-hoc defunctionalization*.  A binder

```fstar
val g : ([@@monomorphize] f : a -> b) -> ...
```

is elaborated, before specialization, into three binders

```fstar
val g : (closure: Type) -> ([@@monomorphize] func : closure -> a -> b) -> (c: closure) -> ...
```

and at a use site the argument `(fun x -> foo x n)`, where `n : UInt16.t` is a
captured `Poly` variable, is elaborated into the three arguments

```
UInt16.t          closure_67          n
```

where `closure_67` is a lifted top-level function
`let closure_67 (c: UInt16.t) (x: a) = foo x c`.  In other words:
monomorphization keys on the defunctionalized *code pointer*, function
parameters become closure-environment parameters, and the original function
arguments become closure-environment *values*.  Captured variables are handled
by the `closure` type parameter, which stays `Poly` — so `g` is specialized per
distinct function body, not per distinct capture.

Consequences to work out in v2:

- The elaboration is a source-to-source pass on the IR that must run before the
  extraction loop, or be fused into it (the lifted `closure_67` is exactly a
  `request` of a fresh name, so fusing is natural).
- Multiple environment variables become a tuple; an empty environment becomes
  `TUnit` (and phase 4's erasure then deletes the parameter entirely).
- Recursive/mutually recursive closures need the lifted function to be part of
  the caller's SCC.

**Non-monomorphized functions must keep working.**  Defunctionalization is
*opt-in*, driven by the `[@@monomorphize]` annotation.  Ordinary
higher-order code — passing a closure to `spawn`/thread creation, storing a
callback in a data structure, returning a closure — must still produce a real
first-class closure.  So the IR keeps `EFun` as a genuine closure-forming node
(§2.2), and the backends must be able to represent one: OCaml natively, C via
karamel's existing closure handling or an explicit environment struct.  This is
also why we cannot simply defunctionalize everything.

---

### 3.9 Worked example: bundled combinators

EverParse 3D generates *bundles*: a record holding several methods that are
built up compositionally.

```fstar
noeq type parser_combinator (ty:Type0) = {
  parse:     bytes -> option (nat & ty);
  serialize: ty -> bytes;
}

let u32 : parser_combinator U32.t = { parse = …; serialize = … }
let seq (#a #b:Type0) (p: parser_combinator a) (q: parser_combinator b)
  : parser_combinator (a & b) = { parse = …; serialize = … }

let three_numbers = seq u32 (seq u32 u32)
```

The desired output is one top-level function per (combinator, method) pair,
each *calling* its sub-combinators' functions, and no `parser_combinator`
value ever materialized.  Today this is hand-rolled with an
`inline_for_extraction` "prelim" definition that is projected field by field.

Custard gets there without the prelim, but the annotation goes on
*wrapper* functions rather than on `seq`:

```fstar
let parse (#a:Type0) ([@@@monomorphize] p: parser_combinator a) (b:bytes)
  : option (nat & a) = p.parse b
let serialize (#a:Type0) ([@@@monomorphize] p: parser_combinator a) (x:a)
  : bytes = p.serialize x
```

and `seq`'s body calls `parse p` / `serialize q` instead of `p.parse` /
`q.serialize`.  `seq`'s own binders need no annotation: rule 5 of §3.1
propagates `Mono` to them, because they flow into a `Mono` position.

Each specialization `parse@<key>` then *is* that combinator's parser.  Sharing
falls out of interning: two structurally identical grammar nodes normalize to
the same key and collapse to one function.  For the example above the emitted
program is

```
parse@t  parse@tuple2  parse@tuple2_2
serialize@t  serialize@tuple2_2  serialize@tuple2
```

— six functions, each a direct call into the next, with the record type,
its constructor and its projectors all removed by dead-code elimination.

Two pieces of machinery were needed to reach that shape, both in §6's
reduction pass, and both about *not* leaving a residue where the projector
used to be: over-applied inlining (the projector is stored eta-expanded, so
inlining it leaves `EApp (EMatch …, args)`) and an iota rule whose pattern
bindings are *substituted* rather than turned into `let`s.  See §6 pass 5.

This is `tests/custard/Combinators.fst`, which additionally round-trips a
value through the generated serializer and parser, so the test checks the
code's behaviour and not only its shape.

## 4. Driver and on-demand loading

Custard is invoked as

```
fstar.exe --codegen Custard --custard_main Main.main [--custard_entry Foo.bar] \
          --custard_backend OCaml|Krml -o out.krml Main.fst
```

`--codegen Custard` is added to the `EnumStr` at
`src/fstar/FStarC.Options.fst:852`.  Unlike the other codegen modes, it does
*not* hook into `maybe_extract_mldefs` (`Universal.fst:448`); instead
`Universal.emit` (`Universal.fst:304`) dispatches to
`FStarC.Custard.Driver.run` once, after typechecking, with the final `TcEnv`
and the dependency graph.

### 4.1 Loading

The entrypoint's module is typechecked/loaded as usual.  Thereafter, when the
extraction loop meets an `lid` whose module is not in the environment, the
loader calls `CheckedFiles.load_module_from_cache`
(`src/fstar/FStarC.CheckedFiles.fsti:73`) for it, and pushes its sigelts into
the `TcEnv`.  The module's own dependencies are *not* eagerly loaded; they are
loaded when (if) they are reached.  The `Parser.Dep` graph is used only to map
module name → file and to validate checked-file freshness.

This is the "on-demand compilation" goal.  Consequences:

- A `.checked` file for a module we never reach is never even read, which is
  where most of the wall-clock win comes from on large developments (Pulse,
  HACL*).
- Modules containing code that cannot be extracted (pure specification
  modules, `Ghost`-only code, unimplementable `assume val`s) are fine as long
  as the entrypoint doesn't reach them.
- Errors become *reachability-relative*, which is a better user experience but
  means CI must pin a set of entrypoints to get coverage.

A `--custard_verify_reachable` mode (off by default) re-checks that every
loaded checked file is up-to-date w.r.t. its source, using the existing
`CheckedFiles.scan_deps_and_check_cache_validity`.

### 4.2 Seeing through interfaces

Custard must see definitions through `.fsti` abstraction boundaries, exactly as
the ML extraction has done since `--cmi` became the default: an abstract
`val sort : ...` in an interface is useless to an extractor, it needs the body
in the implementation.

Concretely, this constrains the loader: **when both `A.fsti.checked` and
`A.fst.checked` exist, Custard must load `A.fst.checked`.**  The naive
"resolve module name to its checked file" lookup returns the interface, which
is what the typechecker wants and what Custard must not use.  So
`FStarC.Custard.Loader` resolves `A` to its *implementation* checked file when
one exists, and only falls back to the interface when the module is
interface-only (`assume val`s realized externally, which then need an §8 rule or
become `DExternal`).

Note the loading order subtlety already documented in
`src/fstar/FStarC.CheckedFiles.fst:341` and `:469` — `A.fst.checked` implicitly
depends on `A.fsti.checked` — so loading the implementation may pull the
interface in anyway; what matters is that the *definitions* visible to
`Env.lookup_definition` come from the implementation.

Three details of the implementation are worth recording, because each of them
silently produced `DExternal`s for a whole library before it was fixed:

- `Parser.Dep`'s file system map is keyed by **lowercase** module names, so
  `Dep.implementation_of deps "Pulse.Lib.HashTable"` answers `None` while
  `... "pulse.lib.hashtable"` answers with the `.fst`.
- "is this module already loaded?" must mean *the implementation is loaded*.
  By the time Custard runs, the driver has loaded the interface of everything
  the entry point depends on, so a test that accepts an interface never loads
  anything.  `Loader.module_is_loaded` therefore looks for a `modul` record
  with `is_interface = false` — unless the module has no implementation at all.
- `Tc.load_checked_module` deliberately *skips* every sigelt of an
  implementation whose name already came from that module's interface
  (`already_loaded_iface_decls`), which is precisely the set of `val`s Custard
  wants to replace by their definitions.  So the loader pushes the
  implementation's declarations a second time with
  `Env.push_sigelt_force`.  For the same reason it does not re-register the
  module in the desugaring environment when the interface is already there:
  that is an Error 47 (duplicate top-level names).

Consequence for users: `noextract`/abstraction in an interface does not hide a
definition from Custard.  This is the same trust posture as the existing
pipeline under `--cmi`, so it is not a new exposure, but it is worth stating.

### 4.3 Interaction with `noextract` and friends

`noextract` (and `noextract_to "Custard"`) means "do not *emit* a definition
for this"; since Custard is demand-driven, reaching a `noextract` definition is
an *error* (with the request chain shown), not a silent skip.  This is a
deliberate difference from the ML extraction, which quietly drops them
(`Modul.fst:729`, `sigelt_has_noextract`).  `inline_for_extraction` /
`unfold` continue to work: they are handled by `Eager_unfolding`/`Inlining` in
the normalizer, so such definitions are simply never requested.

### 4.4 Entrypoints, and why there is no library mode

Two separate things are being named here, and they used to be conflated.

- `--custard_entry` names a **root of the extraction**: Custard compiles
  exactly the definitions reachable from the roots, and a root survives dead
  code elimination even though nothing in the program calls it.  It may be
  repeated.
- `--custard_main` names the definition the generated program **invokes on
  startup**.  There is at most one, and it is a root too, so the common case
  still needs only one option.

A `--custard_entry` may also name a **module** rather than a definition, which
loads the module and takes its initializers (below) as roots without naming
anything in it.  That is the only way to reach a module which exists purely for
its side effects: `FStarC.Hooks` defines nothing anyone calls and does nothing
but install callbacks, and a compiler built without it fails at run time with
"callback not yet set" rather than at compile time.

#### Module initializers

A top-level `let` whose definiens is *effectful* is a module initializer:
`let _ = clear ()` in `FStarC.Options`, `let _ = register_pass ...` in
`FStarC.Syntax.Resugar`, `let _ = iter register_tactic_primitive_step ops` in
`FStarC.Hooks`.  Nothing in the program refers to it, so the demand-driven
loop of §3.3 never reaches it, and dropping it does not merely lose code --- it
silently changes what the program does, since the registration never happens.

So once the closure from the roots is complete, **every module it pulled in
contributes its initializers**, and that may pull in further modules, so the
step is iterated to a fixpoint.  An initializer is requested after everything
it can call, so it lands at the end of the declaration order and OCaml runs the
emitted `let`s in the order they are printed; across a split (§12.9) the linker
runs each file's in dependency order.  What is *not* defined is the relative
order of two initializers in unrelated modules --- F\* gives that no meaning
either.

This is why the note in §7.3's legality table used to say that dead-code
elimination of a top-level `DLet` is always legal.  It is legal only for a
*pure* one.

Omitting `--custard_main` is the normal thing to do when the generated code is
to be embedded in a hand-written wrapper — which is the usual arrangement,
since a generated `main` can only be reached by linking the whole program the
way Custard laid it out.  The generated code then exposes an unstable API on
purpose: the names are mangled and the signatures are whatever the layout
analysis decided, and the wrapper is expected to be regenerated or adjusted
along with it.

Custard targets **standalone programs**.  `--custard_entry` takes a list only
so that a program can have several roots (a `main` plus signal handlers, say),
not so that a library can export its whole API.

Producing a linkable library would mean treating every exported symbol as an
entrypoint, and a `Mono` binder in an exported symbol then has nothing to
specialize against.  There is no good answer to that: emitting a generic
dictionary-passing fallback silently reintroduces exactly the indirect calls
Custard exists to remove.

The right framing is that this is the same constraint as Rust↔C FFI:
parametric types do not cross a language boundary.  A library built with
Custard has to define *specialized entrypoints* — concrete, fully applied
wrappers such as `let sort_u32 = sort #UInt32.t #u32_ord` — and export those.
That is a documentation and idiom problem, not a compiler one.

---

## 5. Type representation

This is the second major goal.  Phase 3 computes, for every requested type, a
**layout**.  A layout is not just a tag: it has to say *which* source field
survives in which target slot, because every constructor application,
projection and pattern has to be rewritten accordingly.  (Knowing only that
`type foo = { a: prop; b: bool }` "is a newtype" does not tell us whether
`Mkfoo a b` translates to `a` or to `b`.)

```fstar
type slot =
  | S_erased                     // field has no runtime representation
  | S_at of int                  // field lives at target position i

type ctor_layout = {
  cl_name:   string;
  cl_tag:    option int;         // None when the type has a single ctor
  cl_slots:  list slot;          // one per *source* field, in source order
  cl_arity:  int;                // number of non-erased fields
  cl_fields: list (string & cty) // the surviving fields, in target order
}

type layout =
  | L_erased                     // no runtime representation at all
  | L_newtype of {
      ctor:  string;             // the unique constructor
      field: string;             // the unique surviving field...
      index: int;                //   ...and its index in the *source* field list
      ty:    cty }               // the payload type = representation of the whole type
  | L_struct  of list ctor_layout
  | L_abbrev  of cty             // a transparent abbreviation, kept as-is
  | L_opaque                     // abstract, or realized by a custom rule
```

(`FStarC.Custard.Layout` is the implementation; `--custard_dump_layouts` prints
the table.)

`cl_slots` is the essential piece: it is the source-field → target-slot map,
and it is needed even in the `L_struct` case, because erasing field `a` from
`{ a: prop; b: bool; c: int }` renumbers `b` and `c` from positions 1,2 to
0,1.  `L_newtype` is then just the degenerate case where exactly one slot is
non-erased; recording `field`/`index` is what disambiguates
`type foo = { a: prop; b: bool }`.

### 5.0 Layouts are uniform in type parameters

**A layout is a function of the type *declaration*, not of an instantiation.**
`foo int` and `foo prop` get the *same* layout.

This is forced on us by parametric polymorphism.  Consider

```fstar
type foo a = { x: a; y: bool }
val f : foo 'a -> foo 'a
```

`f` is compiled once, so the projections and constructions inside it have to
work at every instantiation.  If we let `foo prop` collapse to a newtype (its
`x` field being erased) while `foo bool` stayed a two-field struct, then `f`'s
body would need two different compilations — which is exactly what we are not
doing when a type binder is `Poly`.  So layout precision and type
monomorphization are the same question, and v1 answers it conservatively:

> **Uniformity rule.**  When computing a layout, a field whose type is (or
> contains, in relevant position) a type *variable* is treated as relevant: it
> is never erased and never collapsed away.

The same rule read from the other side says that a type *argument* carries no
runtime information, since it cannot change any layout.  So a type binder that
is still `Poly` after the rule-5 fixpoint is classified `Dropped` (§3.1) and
deleted from the signature and from every call site — whether it was written
implicitly or, as in `let idt (a:Type) (x:a) : a = x`, explicitly.  Under
`--custard_monomorphize_types` the same binders are `Mono` instead and are
consumed by specialization; either way nothing type-shaped survives into a
runtime signature.

`type foo a = { x: a; p: prop }` is still a newtype of `a` — that is uniform,
because `p` is erased at every instantiation.  `type foo a = { x: a; y: bool }`
stays a two-field struct at every instantiation, even `foo prop`.

A polymorphic Custard declaration is not, however, the end of the story for
the C backend: C has no polymorphism.  karamel monomorphizes it, exactly as it
does for the ML pipeline, and to do that it needs the type arguments of every
call.  So although a type argument is deleted from the *value* spine, it is
carried on the `EQual` node as a type application (§2.2), and a declaration
records the type variables it abstracts over in `dl_typars`.  The OCaml backend
ignores both; the karamel backend turns them into `ETypApp` and
`DFunction`'s `n_type_args`.

The rule composes with §2.1 for free: the layout table is keyed by the
*specialized* type name (§2.3), and under `--custard_monomorphize_types` there
are no type variables left, so the uniformity rule vacuously permits maximal
precision.  One rule, two regimes: uniform compilation of types when they stay
polymorphic, per-instantiation layouts when everything is monomorphized.  There
is no middle setting in v1.

#### 5.0.1 The type monomorphization pass

`--custard_monomorphize_types` is two separate things.  Rule 4 of §3.1 makes
every *function*'s type binders `Mono`, which specialization then consumes, so
no function is left polymorphic.  That leaves the polymorphic type
*declarations* the functions mention: `list` is still one declaration with one
parameter, and the program says `TApp (list, [int])` here and
`TApp (list, [bool])` there.  A separate IR-to-IR pass,
`FStarC.Custard.Monomorphize`, gives each distinct instantiation a declaration
of its own.

It is a pass over the IR rather than part of the extractor.  The extractor's
job — deciding what to compile and at what instantiation — is already
delicate, and this needs none of it: by the time the IR exists every type is
ground, so the set of instantiations is simply what is written in the program.
Nested instantiations (`list (list int)`) then fall out of a worklist instead
of having to be threaded through the demand-driven loop.  And it runs *before*
the layout analysis, which is what earns the second regime above: with no type
variables left the uniformity rule is vacuous, and layouts really are computed
per instantiation.

Four things make it work.

1. **Constructor names follow their owner.**  A clone's constructors get the
   *owner type's* suffix — `Prims.Nil` of `list@uint32` is `Prims.Nil@uint32` —
   rather than a suffix of their own.  A use site can then rename a
   constructor knowing only the type it is building or matching, which every
   use site does know.

2. **Patterns are rewritten top down**, against the type the scrutinee had
   *before* rewriting, and the subpatterns against the field types read off the
   original polymorphic declaration with a positional substitution.  That needs
   only the original declarations, so it does not matter whether the clone's
   body has been built yet.  The scrutinee's type comes from an environment of
   binder types, not from the `ty` field of the scrutinee node: binder types
   are exactly what this pass rewrites and so are known precisely, whereas
   `ty` is best-effort metadata (§2.2) that is often `TAny`.

3. **Abbreviations are looked through.**  A type abbreviation is not a
   representation and so is not an instantiation either: `bytes = list uint32`
   has to be unfolded to find the instantiation a use site means, and `nat` has
   to be unfolded so that it does not ask for a different clone than `int`.
   The layout pass unfolds abbreviations anyway, immediately afterwards, so
   nothing is lost by doing it here.

4. **Externally realized types are frozen.**  An external is realized by
   hand-written code in the target language, which this pass cannot rewrite.
   If `FStar.String.concat` is realized in OCaml at `'a list`, then `list` has
   to stay one polymorphic declaration and every use of it has to agree.  So
   every type mentioned in an external's signature is frozen, transitively,
   along with everything reachable from it, and is left alone.  In C, where
   nothing is realized polymorphically, this set is empty — which is why the
   flag delivers a completely monomorphic program there and only a mostly
   monomorphic one under the OCaml backend.

Ordering costs nothing: the clones are appended at the end of the program,
because `Simplify.scc` topologically sorts the whole program — type
declarations included — at the end of phase 4, which is after this pass runs.

`tests/custard/MonoTypes.fst` is the test.  It asserts that two instantiations
of one type become two declarations, that a nested `list (list int)` works,
that an abbreviation and its expansion share a declaration, and that no type
variable survives anywhere in the generated file.

### 5.1 Erasure

A type is erased when it is non-informative.  The existing predicate is
`TcUtil.must_erase_for_extraction` (`src/typechecker/FStarC.TypeChecker.Util.fst:3283`)
→ `Normalize.non_info_norm` → `Env.non_informative`
(`src/typechecker/FStarC.TypeChecker.Env.fst:1080`), which covers `unit`,
`prop`, `squash`, `Ghost.erased`, and anything with the
`must_erase_for_extraction` attribute.  Custard reuses it verbatim, and adds
the *structural* closure:

Erasure of a *binder* is where this gets subtle.  A binder whose sort is
unit-shaped — `unit`, `squash p`, or `_:unit{p}`, which is exactly what
`U.is_unit` recognizes — is deleted from the signature and from every call
site, like any other non-informative binder, **unless** the last-binder guard
of §3.1 rescues it.  A deleted one costs nothing at all; a rescued one is kept
but its argument is replaced by `()`.

Replacing the argument is what keeps ghost code out of the output: the position
is non-informative by definition, so its value is irrelevant, while the term
the source wrote there can be a `Prims.magic ()` that aborts at runtime, or an
arbitrarily expensive proof.  `Mono.unit_binders` computes the mask and
`Extract.value_args` applies it, at both calls and constructor applications.

Deleting these binders is not just cosmetic.  karamel removes `TUnit`
parameters itself (`Simplify.remove_unused_parameters`, "type-based
elimination"), so the C backend never saw them; OCaml does not, so every proof
obligation the source discharged showed up as a literal `()` at every call
site, in code that is meant to be read and checked in.  And the direct-to-C
backend of M8 will not have karamel to fall back on.

#### Erase on sight

Erasure decides what is *not* extracted, so it has to be applied *before* the
term is walked, never after.  A request is a side effect: `Extract.request`
specializes the definition, emits it, and records it, so descending into a
subterm that will later be thrown away still leaves its entire transitive
closure in the program.  The subsequent simplifier deletes only the
*reference*.

Custard therefore short-circuits at three places, each returning the erased
answer without looking at its operands:

- `Extract.erasable_app` — a saturated call whose comp is pure or ghost and
  whose result type is non-informative becomes `()`.  The purity side
  condition is essential: an erased *result* says nothing about side effects,
  so `unit -> ML (erased int)` is extracted normally.
- the `Tm_let` case of `Extract.expr_of_term` — same test on `lbtyp`/`lbeff`,
  so `let x : erased t = <ghost> in e` never visits `<ghost>`.
- `Extract.ty_of_typ` — a non-informative `Tm_fvar`/`Tm_app` collapses to
  `TUnit` instead of requesting its head, which would emit the type's whole
  definition and recursively that of every type it mentions.

On the Pulse hash table this is the difference between 44 emitted declarations
and 27: `Ghost.hide`, `mk_init_pht`, `lift_hash_fun`, `Seq.Base.create`,
`Seq.Base._cons`, `FStar.SizeT.v`, `Prims.op_Subtraction`, `repr_t`, `lseq`,
`Prims.pos` and `Prims.nat` are now never requested at all, rather than
requested, monomorphized, emitted, and swept up afterwards by pass 6.

- a record/variant all of whose fields are erased is erased
  (`type foo = { a: prop; b: prop }` ⟹ `L_erased`);
- a variant with exactly one constructor with no non-erased argument is
  erased;
- an abbreviation of an erased type is erased;
- an arrow whose result is erased and whose effect is `E_Pure`/`E_Ghost` is
  erased (an arrow into `E_Impure` is not, because it may have effects).

One wrinkle: `prop` is `assume val prop : Type0`, so a `prop`-valued definition
such as `Prims.eq2` or `Prims.l_and` cannot be recognized as a type
constructor by normalizing its result to a `Tm_type`.  Custard special-cases
`prop` in `is_type_sig`, and marks every `prop`-valued type constructor erased
outright — being opaque, the structural closure would never discover it.

Note that a *multi*-constructor variant whose fields are all erased is **not**
erased — `type c = | A | B` still has to carry a tag.  It becomes an
`L_struct` with `cl_arity = 0` for every constructor, i.e. an enum.

Unlike the ML extraction, erased things are *deleted*, not replaced by `unit`:
erased fields disappear from records, erased constructor arguments disappear,
erased binders disappear from signatures, erased let-bindings are dropped if
pure, and erased arguments disappear from applications.  Only a residual erased
value in a position that syntactically requires one becomes `TUnit`/`()`.

### 5.2 Newtype collapse

Erasure runs *first*, computing `cl_slots`; newtype collapse is then simply the
observation that a type has one constructor whose `cl_arity` is 1:

- `type foo = | Foo of bar` ⟹ `L_newtype { ctor = "Foo"; field = "_0";
  index = 0; ty = bar }`
- `type foo = { a: prop; b: bool }` ⟹ `cl_slots = [S_erased; S_at 0]` ⟹
  `L_newtype { ctor = "Mkfoo"; field = "b"; index = 1; ty = bool }`
- `type foo a = | Foo of a & unit` ⟹ `L_newtype { …; index = 0; ty = a }`

The rewrites applied by phase 4 all consult the layout, and are total because
the layout records which field survived:

| Before | Condition | After |
| --- | --- | --- |
| `ECtor (Foo, es)` / `ERecord (foo, fs)` | `L_newtype {index=i}` | `es[i]` — the other arguments are dropped, after hoisting any that are effectful (§7.3) |
| `EProj (e, Foo, "b")` | `L_newtype {field="b"}` | `e` |
| `EProj (e, Foo, "a")` | `L_newtype`, `a ≠ field` | unreachable: `a` is erased, so the projection was already deleted by §5.1 |
| `EDiscrim (e, Foo)` | single constructor | `true` |
| `EMatch (e, [PCtor (Foo, ps) → body])` | `L_newtype {index=i}` | bind `ps[i]` to `e`; the other `ps[j]` are erased and bind nothing |
| `TApp (foo, args)` | `L_newtype {ty}` | `ty` (instantiated at `args`) |
| `ECtor (Foo, es)` | `L_struct` | `ECtor (Foo, [es[j] | cl_slots[j] = S_at _])`, reordered by slot |
| `EProj (e, Foo, "b")` | `L_struct` | projection at slot `cl_slots[b]` |

So the answer to "do we translate `Mkfoo a b` to `a` or `b`?" is: to whichever
one `cl_slots` maps to `S_at 0`, and the layout is computed once per specialized
type and consulted by every rewrite.

Guards:

- A type marked `[@@no_newtype]` (or `CAbstract`, or given a hand-written
  target realization) is left alone.
- A field whose type is a type variable is never erased (§5.0), so
  `type foo a = { x: a; y: bool }` never collapses, at any instantiation.
- Newtype collapse of a *recursive* single-constructor type must not be
  performed when it would produce an infinite type
  (`type t = | C of t`); such types are `L_struct` (and are in fact
  uninhabited, so a warning is appropriate).
- Collapse is computed as a fixpoint over the SCC of type dependencies, since
  `foo`'s layout feeds into `bar`'s.
- Dropping the non-surviving arguments of a collapsed constructor application
  is only sound when they are pure; if an argument is `E_Impure` it must be
  hoisted into an enclosing `ELet`/`ESeq` first, not discarded (§7.3).  The
  same applies to erased-but-effectful arguments in §5.1 — in practice these
  only arise from `Ghost`/`Pure` computations and so are droppable, but the
  pass must check rather than assume.

Because Custard has no ABI-compatibility obligation (an explicit non-goal),
this is safe: nobody outside the generated program can observe the
representation, except through the custom rules of §8, which opt out.

Collapse takes precedence over the inline fields of §5.7, and takes the
marker with it.  `type step = | Step of bool & string` is a single field of
tuple type, so §5.7 marks it inline; but the constructor disappears
altogether, and `step` simply *is* the pair — a strictly better answer than
inlining into a wrapper.  The marker has to be stripped as the payload is
recorded, because a collapsed type is substituted for its name *everywhere*,
including into binder types and type arguments, and `Simplify.inline_fields`
only ever looks at constructor fields.  Left on, the marker escapes to
positions no pass will visit and reaches a backend that has no representation
for it.

### 5.3 The layout fixpoint

Erasure and newtype collapse interact with the extraction loop: whether a
binder is dropped depends on whether its type is erased, which depends on the
type having been extracted.  The implementation splits this in two.

*Binder* erasure is decided during extraction (phase 2), where the F* type is
still available: `Mono.classify` gives a binder the class `Dropped` when
`TcUtil.must_erase_for_extraction` holds of its sort, and the argument is then
deleted at every call site by the same `split_mono_args` that handles `Mono`
arguments, so the two sides cannot drift apart.  Unit-shaped binders go the
same way, subject to §3.1's last-binder guard, which is what keeps a genuine
thunk from being deleted.

*Type* erasure and collapse are decided after extraction, over the whole IR, by
a **least fixpoint** starting from "nothing is erased" and iterated until
stable (bounded by the number of type declarations).  Least, not greatest, is
what makes a recursive type answer "not erased", which is the safe direction.
Newtype candidates are computed from the resulting `cl_slots`, and a candidate
whose representation can reach itself through other candidates' representations
is rejected, which is the `type t = | C of t` guard.  Term-level rewriting only
happens afterwards, so no rewrite is ever done on a stale assumption.

### 5.4 Coercion elimination

`ECast` nodes come from three sources: source-level `Obj.magic`/`coerce_eq`,
`Ghost.reveal`/`hide`, and the subtyping mismatches that Custard itself
introduces (mostly around `TAny`).  Phase 4 runs:

1. `ECast (e, t)` → `e` when `layout t = layout e.ty` (after collapse);
2. `ECast (ECast (e, _), t)` → `ECast (e, t)`;
3. push casts towards the leaves so that (1) fires more often.

Rules 1 and 2 are implemented, in `Layout.rw_expr`.  Rule 3 is **not
implemented, and as of M6h has nothing to bite on**: no `ECast` at all survives
to the backend, anywhere in the test corpus (all sixteen `tests/custard`
modules and both Pulse tests, including `PulseHashTable`, which is exactly the
`repr`-over-erased-index style this section is about).  The generated OCaml
corpus contains no `Obj.magic`.  That is the goal met, not a gap, so rule 3 is
deferred until an input demonstrates it is needed.

The reason is that two of the three sources above never reach phase 4:

- `Ghost.reveal` is `GTot`, so §5.1's erase-on-sight removes the call before it
  can become a cast.  (F\* will not even let you write a `Tot` wrapper around
  it.)
- `coerce_eq` extracts as an ordinary polymorphic identity function, which
  monomorphization then specializes and inlining then deletes.

The machine-integer rules in `Builtins` produce `ECast` too, and those are not
lost information at all: they are the conversion the source asked for, a real
call into `FStar.Int.Cast`.  Rule 1 must not delete them, and rule 3 could only
duplicate them across branches.

`--custard_warn_any` (§5.9) is what turns "we measured zero" into something
that stays true.

#### Coercion *insertion* (`Simplify.coerce_prog`)

The measurement above holds for the test corpus and stopped holding for the F\*
compiler itself.  `FStarC.Class.Monad` is a class over a type *constructor* —
its `m` has kind `Type -> Type` — so `m a` is not an application of anything
the IR's type language can name and its dictionary fields land on `TAny`.
Monomorphization cannot help: `m` is not a `Mono` argument and could not be
one, since a `Mono` argument stands for a value.  OCaml has no name for it
either, so `TAny` prints as `Obj.t`, and something has to tell OCaml's type
checker to stop looking.  That something is `Obj.magic`, and there is no
avoiding it — `m t` is genuinely not an OCaml type.

So the no-generated-`Obj.magic` property is a *goal*, not an invariant: the
thing to minimise is `TAny`, and where a `TAny` genuinely remains, a coercion
is the correct output.  What is still ruled out is the ML extraction's
characteristic noise — a coercion around an `if` *and* another around each of
its branches, `unit` to `Obj.t` and back — which is what made its output
unreadable and unauditable.

`coerce_prog` is the last pass in `Simplify.run`, after everything that can
change a type.  It is a bidirectional walk: `check` pushes an expectation down
from a boundary, `infer` pulls a type up towards one, and a coercion goes in
where both are known and `cty_mismatch` says they disagree.  `cty_mismatch` is
structural and fires *only* on a `TAny` against a concrete type; two different
concrete types are not this pass's business, since either the IR is well-typed
and they agree up to something `Layout` resolved, or it is not and a coercion
would hide the bug.  A `TVar` agrees with everything, uniform compilation being
exactly the statement that a type variable's representation is uniform.

The subtlety is **which types the pass is allowed to believe**, and the answer
is not "the `ty` field on every node".  A node's `ty` is what `Extract` could
work out at the time, and a `TAny` there means "not worked out" as often as it
means "no representation": a call to a not-yet-emitted recursive function falls
back to `TAny` in `callee_sig`, and so does a head a builtin rule rewrote.
Driving the pass off those produces a coercion at almost every application —
which is precisely how the first implementation behaved, and precisely the
output this pass exists to prevent.

The types that are *not* guesses are the ones a backend prints:

- a declaration's `dl_binders` and `dl_ret`, and an external's `dx_ty`;
- a constructor's and a record's field types;
- and nothing else.  A lambda binder is not annotated in the output, and
  neither is a `let`; their `TAny`s were never claims.

So those are the boundaries.  Everywhere either side is unknown, nothing is
inserted: OCaml infers, and a coercion would only be noise.  A node's own `ty`
is still used, but only when it mentions no `TAny` at all — the case where it
is trustworthy, because `Extract` falls back but never invents.

Two rules fall out of that and are worth naming:

- **A coercion *to* `TAny` needs much weaker evidence than one *from* it.**
  `Obj.magic e` is well-typed in the target whatever `e` turns out to be.  So
  when a term of unknown type reaches a position declared `TAny`, it is enough
  to know that the term obviously has *some* representation — it is a
  constructor, a record, a tuple, a constant, a lambda, a primitive operation.
  This is what makes the `Class.Monad` case work: `Some x` built at type
  `option Obj.t` has a node type mentioning a `TAny` that says nothing about
  the `option`.
- **A node that hands its expectation to its own result does not get asked
  again.**  `ELet`, `ESeq`, `EIf`, `EMatch` and `ETry` all push the expectation
  down to the terms that produce their value, so each of those has already been
  coerced and the node agrees by construction.  Asking a second time is exactly
  how a coercion ends up around the `if` as well as inside each branch.

A scrutinee, a projection and a discriminator are the one place the expectation
is manufactured rather than read off: a value of type `Obj.t` cannot be taken
apart until it has a representation, so it is coerced to the head of the type
the pattern or the field name belongs to.  Its arguments are unrecoverable and
come out `TAny`, which is honest — and the target needs only the head, since
OCaml infers the rest from the pattern.  The guard is `TAny` *exactly*:
`list Obj.t` is matched and projected perfectly well as it stands.

Finally, `PrintOCaml` spells a coercion to or from `TAny` as a bare
`Obj.magic`, at every width and every depth.  It must not change the
representation, or the two directions would have to agree about which one is
canonical — and they cannot, because the same value also crosses the boundary
*inside* a structure (`uint32 list` to `Obj.t`), where no per-element
conversion is possible.  A coercion between two machine integers is still the
`FStar.Int.Cast` call described above.

`tests/custard/Magic.fst` pins the result: a two-method class over
`Type -> Type`, an `option` instance, one generic user and one concrete call
site.  Its `GREP`/`NOGREP` pair requires a coercion at each of the three real
boundaries and forbids one around the `match`.

### 5.5 Record recovery

Extraction reads ML syntax, which has already forgotten which of F\*'s
inductives were written as records: everything arrives as a `TVariant`, and
every field read arrives as a one-branch `match`.  Nothing produced a `TRecord`
at all, even though the IR has the node and every backend prints it.

Undoing that in each backend is both duplicated work and not enough.  The C
backend can compile a one-branch match into nothing (§6), so it looked fine;
the OCaml backend cannot, and `PulseHashTable.lookup` came out with seven
copies of

```ocaml
(match ht with Mkht_t (sz, hashf, contents) -> sz)
```

where `ht.sz` was written.  So the recovery is a pass on the IR, `records` in
`Simplify`, run last.  It has two halves.

**Match-to-projection (`depat`).**  A `match` with a single branch, no guard,
and a pattern `C x1 … xn` where `C` is the *only* constructor of its type and
every subpattern is a variable or a wildcard, is not a control-flow construct:
it is a set of field reads.  It becomes the branch body with each `xi`
replaced by `EProj (scrut, C, fi)`.

Re-reading the scrutinee once per field is only free when the scrutinee is a
variable, a constant, a top-level reference, or a projection out of one;
otherwise it gets a `let` first, which is exactly what was already there.

The substitution deliberately does *not* rename the binders it passes under,
unlike the one used for inlining.  Inlining copies a definition into a scope
that may already use its names; here the body stays where it is, and what is
substituted into it are projections out of variables bound outside it, so
nothing can capture.  Not renaming is what keeps `sz` from becoming `sz_41`.

A field read printed as `e.lbl` is where OCaml's own record resolution takes
over, and it resolves a *label*, not a type: two record types in the same module
that share a label name send every unannotated use to whichever was declared
last, silently.  Qualifying the label names the module, not the type, so it does
not help.  `PrintOCaml.ascribe_record` therefore ascribes the target,
`((e : _ _ Mod.t)).Mod.lbl`, and does the same for a record expression.

It ascribes only when the label really is contested — a table built alongside
`record_params` counts, per module, how many record types declare each label —
because otherwise the annotation is on every projection in the program.  Whole
compiler: 50 ascriptions, all of them `lazyinfo` and `sub_eff`.  Specializations
count as distinct types, so `both__int` and `both__bool` do make `fst`
ambiguous, and are ascribed.

Projections need this more often than record expressions do, not less: a record
expression at least names all of its labels at once, whereas `x.uniq` names one,
and the only other thing that could decide the type is what `x` is already known
to be — which, in a lambda Custard emits without binder annotations, is nothing
at all.  It surfaced when `FStarC.Reflection.V2.Embeddings.e_namedv_view`
stopped being specialized: its `embed` closure only projects `uniq`, `sort` and
`ppname`, which `binding` also declares and declares later, so the closure was
inferred at `binding` and no longer agreed with its own `unembed`.

The same pass replaces `EDiscrim (e, C)` on a one-constructor type by `true`
when `e` is pure.  That is worth doing on its own — the OCaml backend prints a
discriminator as a whole `match` — but it also matters for the second half,
which cannot fire while a discriminator still names the constructor.

**The conversion.**  A one-constructor type with at least one field becomes a
`TRecord`; its `ECtor` becomes an `ERecord` and its `PCtor` a `PRecord`.  The
verdict is a function of the declaration alone, and nothing else — see the
representation principle below.

That was not always so.  The IR originally had no record *pattern*, so a type
that any surviving `PCtor` still matched had to stay a variant; and since
whether one survives is a fact about the whole program, so was the verdict.
Adding `PRecord` (which every backend has: OCaml prints `{ f = p; _ }`, karamel
already had the node) removes the condition, and with it the reason `depat` had
to skip constructors that some *other* match still mentioned refutably.

The conversion is unconditional in the field names.  F\* names the arguments of
a non-record constructor `_0`, `_1`, …; those are legal field names in all
three backends, and converting them too is what guarantees no `EProj` anywhere
points at a variant.  One consequence worth knowing: `Rename` keys a record's
fields on the *type* name and a variant's on the *constructor* name, so the
pass re-tags every `EProj` it converts.

The C backend already treated a one-constructor variant as a plain struct, so
its output is byte-for-byte unchanged; the win is entirely in OCaml and
karamel.  What stays in the C backend is what is genuinely target-specific:
dropping unit parameters (OCaml needs `()` to delay an effect), `void` returns,
not testing the last match arm (OCaml checks matches syntactically), the brace
and hoisting peepholes, and turning a one-cell stack allocation into a
variable (which needs `&x`, and so has no ML analogue).

**Where the decision lives.**  Both this verdict and §5.7's plan are computed
in `Layout`, from the declarations alone, and recorded in the `verdicts` table
`Layout.run` returns alongside the program.  `Simplify.records` and
`Simplify.inline_fields` are pure appliers: they look a constructor up and
rewrite, and decide nothing.  The principle they exist to enforce is

> a type's representation is a function of the type and of the types it is
> built out of, and of nothing else.

Anything derived from the program as a whole is a different answer in a
different unit, and two units that disagree about a representation while
agreeing about a name is a miscompilation no signature check can catch (§12.5).
The escape hatch of simply not exporting a reshaped type is not available:
global variables and exceptions need *nominal* identity across units — a
downstream copy would write to a different global, or throw an exception the
upstream `try` cannot catch — so every declaration has to be exportable, and
therefore every verdict has to be reproducible.

Where the appliers sit in the pipeline is then a question of code quality
alone, and they still run late (§6), because the projections they feed on are
mostly what `depat` leaves behind.

**Which record type an OCaml record expression has.**  OCaml resolves a record
expression from its labels, and when two record types in the same module share
their labels --- `namedv_view` and `binding` in `FStarC.Reflection.V2.Data` both
have `uniq`, `sort`, `ppname` --- it takes the one declared *last*, unless the
expression's type is already known from context.  Qualifying a label names the
module, not the type, so it does not help.  `PrintOCaml` therefore ascribes
every record expression, `({ ... } : (_, _) t)`, with the parameter count read
off the type's own declaration.  The ML extraction gets away without this only
because the shapes it emits usually have an expected type to hand; Custard's do
not, and the failure is silent whenever the two types happen to be
representation-compatible.

### 5.6 Unreachable branches

`EAbort` says control does not reach here, and it means it: the only rule that
introduces one is Pulse's `unreachable` (§8.3), whose precondition F\* has
already proved false.  A branch whose body is nothing but an abort therefore
contributes nothing to the value of the match, and testing for it is wasted
work at run time and noise in the output.  `prune` drops such branches, and
rewrites `if c then e else abort` (and its mirror) to `e`, keeping `c` as a
statement if evaluating it is observable.

A match *all* of whose branches abort is left alone: it cannot be entered, and
there is no value to give it.

This started as a C-backend peephole, where dropping a branch also lets the one
before it become the unconditional one.  But the reasoning has nothing to do
with C — the branch is dead in every target.  What made it safe to lift is that
Custard already relies on F\*'s exhaustiveness check rather than on the target's:
the generated OCaml disables warning 8 in its header, and `--ocamlopt` passes
`-w -8` for the same reason.  Running it before §5.5 also matters: dropping a
branch can leave a match with a single irrefutable one, which §5.5 then removes
entirely.

### 5.7 Inline fields

`| Bar of a & b` is how F\* source spells a two-argument constructor, but it is
not what it means.  What it means is a constructor with *one* argument, whose
type is `a & b`, so every `Bar` is two allocations and every read of a field
two loads (FStarLang/FStar#4382).  The same is true of `| K of pair` for a
record `pair`, except that there the author may well have meant it.

An **inline field** stores the field's record in the constructor itself:

```
type foo = | Bar of bool & string      (*  Bar of bool * string  *)
noeq type wrap =
  | W : [@@@custard_inline_field] p:pair -> wrap
                                       (*  W of bool * string    *)
```

The policy is in `Extract` and the mechanism in `Simplify.inline_fields`.
`Extract` inlines a field whose type is one of `FStar.Pervasives.Native.tupleN`
without being asked, on the grounds that the pair in `| Bar of a & b` is never
what the author was after, and any other field on `[@@@custard_inline_field]`.
It says so by wrapping the field's type in `TInline`, which rides along through
every pass that rewrites field lists without any of them having to know about
it.  `Simplify.inline_fields` is the only consumer and removes every marker it
finds, whether or not it could act on it; no later pass and no backend ever
sees one.  (The two places that read a *declared* field type for some other
purpose — `Monomorphize.ctor_fields`, which types the subpatterns of a `PCtor`,
and `Simplify.ctor_infos`, whose types end up on `EProj` nodes — strip it, since
there the marker has no meaning.)

For a field `f` of constructor `C` whose type is a record `R` with fields
`g1..gn`, the pass does four things.

- The **declaration**: `f` is replaced by `n` fields.  Their types are `R`'s,
  instantiated at the arguments `f` was applied to, since Custard also runs
  without `--custard_monomorphize_types`.  Their names are `f_gj`, except that
  a constructor all of whose fields are the positional `_0`, `_1`, ... — which
  is to say, every `| Bar of ...` — keeps positional names, renumbered.
- **Construction.**  `ECtor (C, [.. e ..])` splices `e`'s fields in when `e` is
  a value of `R` that is right there, which is the common case: `Bar (Mktuple2
  (b, s))` becomes `Bar (b, s)`, and nothing is allocated that was not going to
  be.  Otherwise it splices in `n` projections out of `e`, `let`-binding it
  first if re-evaluating it is not free.
- **Patterns.**  `PCtor (C, [.. PCtor (Mk_R, qs) ..])` splices `qs` in, which is
  the case that pays.  A `PWild` becomes `n` wildcards.  A `PVar v` standing for
  the whole field becomes one variable per piece, and the body gets `v` back as
  a reconstructed `R` — substituted when every use of it is a projection, so
  that the reconstruction is taken apart again and never built, and behind a
  `let` otherwise, so that no allocation is duplicated.
- **Projection.**  `EProj (e, C, f)` has to rebuild an `R` out of the `n`
  fields.  Chained through a further projection this costs nothing, because the
  pass finishes by reducing every `EProj` out of a value that is right there.

Each of the residual cases is correct but no faster than before, which is what
makes the pass safe to apply without measuring.

The plan is computed in `Layout` and is a function of the declaration and of
the declaration of the field's type: `Extract` put the `TInline` marker there,
and the rest is a lookup.  There used to be one whole-program ingredient — a
field was taken out of the plan everywhere if any pattern in the program
matched it against something that could not be flattened — but `Extract` only
ever emits `PWild`, `PVar`, `PConst` and `PCtor`, and at a record-typed
position `PConst` is impossible while the other three are all handled, so that
scan was defensive and is gone.

The *rewriting* runs after `depat`, and that ordering is a code-quality
question: a field of `R` is read with an `EProj` only once `depat` has turned
the irrefutable match into projections, and that is what lets the rewriter see
that a reconstructed value will never actually be built.  It runs before
`records`, because a plan is expressed in terms of the constructor holding the
field, which is exactly what `records` removes.

Two things that look like they need this and do not.  `| Baz : x:a -> y:b -> t`
is already a two-field constructor — the `of` syntax is the only one that
introduces the pair.  And `| Bar of { x:a; y:b }` is not F\* syntax at all, so
there is nothing to inline there.

### 5.8 Other representation choices (to be pinned down)

- Machine integers: `UInt32.t` etc. must map to native target types, not to
  their `nat`-refinement definitions.  Handled as custom rules (§8), the same
  way karamel does it today.
- `option`/`either`/tuples: `option t` where `t` is a pointer type is a
  candidate for null-pointer representation in the C backend.  Deferred.
- Refinement types are erased to their base type (they are already erased by
  the normalizer's `Unrefine`/`ForExtraction`).

### 5.9 `--custard_warn_any`

`--custard_warn_any` walks the final IR, after renaming so the names it reports
are the ones in the emitted file, and warns (code 366) about the two ways
Custard can lose track of what a value looks like at runtime:

- a **`TAny`** anywhere in a declaration's binder types, result type, `ELet`
  binding type, lambda binder types, record or variant field types, or external
  declaration type.  `TAny` is the analogue of the ML extraction's `MLTY_Top`;
  in a whole, monomorphic program there is almost always an answer, so an
  occurrence is a place something went wrong upstream.
- a surviving **`ECast`** whose two sides are not both machine integers.

One warning is emitted per declaration, listing its sites, rather than one per
occurrence: the IR has no source positions, so a flat list of anonymous
occurrences would be unusable.  The code is a `CWarning`, so `--warn_error @366`
escalates it; the test suite runs the whole corpus that way, which is what
makes the measurement above a checked invariant rather than a note.

Deliberately **not** checked is the `ty` field of arbitrary expression nodes.
That field is best-effort metadata — `callee_sig` falls back to `TAny` for a
callee whose signature is not to hand, and the fallback propagates through
`apply_result` — and neither backend consults it except in a handful of places
where it is already guarded.  Checking it flagged even `Hello`, which is the
definition of a useless diagnostic.  What is checked is exactly the set of
positions that shape the generated code.

Two things the flag found on first use: primitives that had to be
eta-expanded were giving their introduced binders `TAny` rather than the
primitive's own remaining binder sorts (fixed, `Mono.retained_sorts`), and
higher-kinded polymorphism (`#f:Type0 -> Type0`, `x: f int`) has no
counterpart in the target type language and lands on `TAny` throughout — which
is the honest answer, and now a visible one.

### 5.10 Local `let rec`

A local `let rec` is lambda-lifted to a top-level `DLet` rather than given an
IR node of its own.

The IR's `ELet` is documented non-recursive, and adding an `ELetRec` would mean
teaching every traversal about it.  There are ~57 `ELet` sites across a dozen
files, half of them in `Simplify`, and many traversals end in a catch-all
`| _ -> x`; since `src/custard` is built with `--lax`, which does not check
match exhaustiveness, a pass that failed to learn about the new node would
silently drop or mistraverse it rather than fail to compile.  A lifted function,
by contrast, is an ordinary declaration: it gets specialization, `Simplify.scc`'s
recursion analysis, and all three backends for free.  It also sidesteps the fact
that a local `let rec` is a closure and C has no closures.

The lifting is the textbook one, with two Custard-specific wrinkles.

*Captured values* become extra **leading** parameters, shared by every member of
a mutually recursive nest, so that the nest stays mutually recursive after
lifting and its members agree on their prefix.  *Captured type variables* become
`dl_typars`, and the use site passes them as `TVar`s of the same names; since
compilation is uniform in type parameters (§5.0) they cost nothing at runtime.

Nothing is renamed.  `Subst.open_let_rec` has already made the local names
unique, and a capture keeps its own name as a parameter, so an occurrence reads
the same inside the lifted body as it did in place.  The lifted declaration is
named after the enclosing declaration, `<enclosing>__<ppname>`, uniquified
through the same counter as every other emitted name; `LocalRec.rev1`'s inner
`aux` becomes `localRec_rev1__aux`.  Lifted declarations are pushed straight
into the emission list — nothing will ever `request` them — and carry a
provisional `Rec` flag naming the whole nest, which `Simplify.scc` recomputes
from the final call graph exactly as it does for top-level recursion.

Occurrences of a lifted name in the body of the enclosing definition become
`EQual (nm, tyargs)` applied to the captures.  The partial application is pure:
the binders the user actually wrote are always still missing.

### 5.11 Polymorphic local functions are inlined

A non-recursive local `let` whose definition is a lambda **that binds at least
one type** is substituted at its uses rather than compiled as a closure.

A local function is the one construct with no top-level identity: it cannot be
specialized, because specialization is keyed on a `lid`, and it cannot be
annotated, because `[@@monomorphize]` is read off a top-level signature.  So
its type parameters and its arguments are whatever its single definition site
says they are — runtime-opaque — and *every* call it makes into a specializing
definition is a §3.2b rejection.  Substituting it gives each use its own
instantiation, which is what the author meant and what a monomorphizing
compiler owes them.

This is not a corner case.  `FStarC.TypeChecker.Primops.Sealed.ops` is
written as

```fstar
let try_unembed (#a:Type) (e:embedding a) (x:term) : ML (option a) =
  try_unembed x id_norm_cb
in
match try_unembed e_any ta, try_unembed (e_sealed e_any) s, ... with
```

— a local helper fixing one argument of a specializing function and used at
several types.  Inlined, each use instantiates `a` concretely and the whole
thing specializes; left alone, it is a hard rejection with no annotation
available to fix it.

Two details matter in the implementation:

- The test reads the definition's shape through `unmeta`.  A local helper
  inside an `ML` definition arrives as `Meta_monadic_lift (PURE, ALL)` wrapped
  around its `Tm_abs` — the lift of a pure *value* into the ambient effect.
  It carries no computational content, but it hides the lambda from a naive
  `compress`-and-match, which is enough to make the whole pass silently do
  nothing.
- `lbeff` is *not* consulted.  Binding a lambda builds a closure and is pure
  whatever the function goes on to do; `lbeff` reports the function's own
  effect, which is `ML` for most local helpers.

#### Why only the polymorphic ones

The restriction is not a heuristic to limit code size; it is the scope of the
argument above.  Inlining is worth doing because it gives a local function's
*type* arguments a concrete value at each use, and that is the one thing a
local function cannot obtain any other way.  A local function with no type
binder has nothing to gain: it is already fully monomorphic, and substituting
it only copies code.

Inlining every local lambda is not merely wasteful, it does not terminate on
real input.  A helper used twice is duplicated twice, inlining runs on the
result of inlining, so helpers that nest cost 2^n:

```fstar
let a y = y + x in
let b y = a y + a (y+1) in
let c y = b y + b (y+1) in ...
```

Pointed at `FStarC.TypeChecker.Normalize.normalize`, the unrestricted version
consumed 73GB without finishing.  What identifies the cause — and rules out
the more obvious suspects — is that **no new specializations were being
requested** while it ran away.  So it was not a runaway request loop (§3.6's
budget bounds those, and none of it was being spent), and it was not a
diverging normalization either: it was already-named code being re-extracted
exponentially often.  Restricted to the polymorphic case, the same run
finishes in ten seconds, and `term_to_string` returns to exactly the size it
had before §5.11 existed — every line the unrestricted version added was
duplication.

`tests/custard/LocalPoly.fst` pins both halves: the polymorphic helper is gone
from the output and specialized per type, and the four nested monomorphic
helpers are still there, once each.

A local `let rec` cannot be substituted and is lambda-lifted instead (§5.10).

---

## 6. Simplification and emission

Phase 4 passes, in order:

1. **ANF / let-normalization** (allowed by the non-goals), in `Simplify.anf`.
   This runs **first**, not last.  The invariant it establishes is: *every
   operand is pure*.  An impure computation may appear only as the right-hand
   side of an `ELet`, the left of an `ESeq`, or in tail position — never as an
   argument, a constructor field, a scrutinee or a cast operand.  So effect
   order becomes explicit, "may I reorder these?" becomes a question about
   statement order rather than about arbitrary subterm positions, and all the
   later rewrites operate on pure operands only.  It also happens to be what
   the C and Krml backends want.

   Hoisting is only sound into a position that is evaluated unconditionally,
   exactly once, where the operand was, so the traversal stops at every delayed
   position: a lambda body, the arms of an `EIf`, the branches and guards of an
   `EMatch` or `ETry`, both parts of an `EWhile` (the condition is re-evaluated
   per iteration), and — because both backends short-circuit them — every
   operand but the first of `And` and `Or`.  The last of those is guarded on
   the operator's *width*: at a width, `And` and `Or` are the bitwise
   operators, which are strict.

   Short-circuiting is worth stating separately, because it is a place where
   Custard has to preserve a semantics rather than choose one, and two
   different mechanisms are responsible.

   - When an operand is **effectful**, F\* has already rewritten `a && b` into
     `if a then b else false` — the connectives are `Tot` functions, so an
     effectful operand cannot be passed to one — and Custard never sees an
     `EOp` at all.
   - When both operands are **pure**, the connective survives as an `EOp`, and
     short-circuiting is still observable, because pure does not mean total:
     F\* discharges the precondition of `100 / x` in `x <> 0 && 100 / x > 5`
     precisely by reasoning that the right operand is not reached.  Evaluating
     it strictly would divide by zero — an exception in OCaml, undefined
     behaviour in C.

   Both backends get this right, and both are emitted infix: `a && b`, not
   `((&&) a b)`.  OCaml would in fact short-circuit the prefix form too — `&&`
   is the `%sequand` primitive, which the compiler lowers to a conditional when
   it is fully applied — but nothing in the emitted file says so, and a reader
   checking the generated code should not have to know it.
   `tests/custard/ShortCircuit.fst` covers both mechanisms and the bitwise
   guard; `KrmlBasic.fst` covers the C side.

   **Most of this work is already done for us, and the exception is the point.**
   An application whose arguments have an *F\** effect arrives in monadic normal
   form, because that is how the typechecker elaborates it; the same is true of
   Pulse, which sequences every `stt` computation through `bind`.  What does
   *not* arrive normalized is everything Custard alone considers impure — an
   arrow promoted by `extract_as_impure_effect` (§7.2), which F\* sees as `Tot`
   and therefore leaves nested.  `tests/custard/Anf.fst` is exactly that shape,
   and without this pass it prints `ba` where the program says `ab`, because
   OCaml evaluates arguments right to left.

   The invariant is also what lets three existing rewrites stop hedging:
   `Layout.hoist` sequences a dropped erased argument before the *whole* node it
   was dropped from, stepping over the arguments to its left; `ctor_args_pure`
   refuses to fire iota at all when any field of the scrutinee is impure,
   because it cannot tell which fields the pattern discards; and `inline_call`
   can only substitute a pure argument, so an impure one blocks the
   beta-reduction that would have consumed it.  After ANF the operands are
   variables in all three cases, so nothing is ever moved past an effect, and
   the last two get strictly stronger.
2. **Erasure/newtype rewriting** (§5.1, §5.2).
3. **Coercion elimination** (§5.4).
4. **Inlining of `Inline`-flagged declarations.**  A declaration carrying the
   `Inline` flag is substituted at each of its *fully applied* uses and then
   dropped.  The extractor sets the flag on the projectors and discriminators
   F* derives for an inductive: each is a single field read or tag test, and
   left as a call it makes both the OCaml and the C output unreadable and
   slower, with no way for a backend to undo it.  A use that is not fully
   applied, or that precedes the definition, keeps the declaration alive
   instead of being eta-expanded.

   Two details matter for correctness.  The copied body's own bound variables
   (lets, lambdas, pattern variables) are **renamed**, because inlining the
   same declaration twice into one caller would otherwise put two bindings of
   the same name in scope — harmless in OCaml, but the karamel backend turns
   names into de Bruijn indices.  And an argument is substituted directly only
   when it is atomic, or pure and used at most once; otherwise it gets a
   `let`, which the next pass removes again if the parameter turns out to be
   unused.  Duplicating an impure argument would duplicate its effect, and
   duplicating an expensive one would duplicate its cost.

   Inlining is preceded by an **eta reduction** of the declarations, because
   F* stores the projector of a field whose type is an arrow eta-expanded:

   ```fstar
   let __proj__Mkht_t__item__hashf projectee x = (match projectee with ... ) x
   ```

   That extra binder makes every use of the projector under-applied, so the
   `Inline` pass declines it and the C backend sees a call with too few
   arguments.  Dropping a trailing binder that is applied to a pure head, and
   occurs nowhere else, is always sound; the arrow it used to consume moves
   back into the result type, and the effect of the arrow it removes becomes
   part of the returned closure's type rather than the declaration's.

5. **Reduction** (beta and iota).  Inlining a declaration can expose a redex
   that neither pass alone will contract, and the leftovers are exactly the
   ones a reader notices.  Two rules, applied to fixpoint together with the
   recursive descent:

   - **beta**: `EApp (EFun (bs, body), args)` with `|bs| ≤ |args|` contracts,
     reusing the inliner's substitute-or-`let` heuristic so an impure or
     multiply-used argument is not duplicated.  Surplus arguments are
     re-applied to the result.
   - **iota**: `EMatch (ECtor (c, es), branches)` selects the first branch
     whose pattern matches, provided every `es` is pure — otherwise selecting
     a branch would drop the effects of the fields the pattern ignores.
     Guarded branches are never selected, since the guard has to run first.

   Two subtleties, both found while getting §3.9 to come out right:

   *Inlining must handle over-application.*  A projector for a field of arrow
   type is stored eta-expanded (see pass 4), so after eta reduction it is a
   one-binder function returning a `match`, and every use applies it to the
   record *and* the method's own arguments.  If the inliner declines
   over-applied uses, the projector survives; if it splits the argument list
   and re-applies the surplus, the result is `EApp (EMatch …, args)`, which
   iota then collapses.

   *Iota must substitute, not bind.*  Turning the matched pattern's variables
   into `ELet`s looks equivalent and is not: it puts an `ELet` where the head
   of the enclosing application was, so the beta rule above never sees the
   `EFun` it is wrapping and every emitted body keeps a residual
   `(fun b -> …) b`.  Routing the bindings through the same
   substitute-or-`let` helper the inliner uses makes a field that is used once
   — the overwhelmingly common case, since the whole point is to select one
   method out of a bundle — substitute directly.

   A third rewrite belongs to the same family, though it is a recovery rather
   than a reduction: **a boolean match becomes an `EIf`**.  The IR has had an
   `EIf` node, and both backends have printed it, since M0 -- but nothing ever
   *built* one, because F\* desugars `if c then a else b` to
   `match c with | true -> a | _ -> b` and Custard faithfully translated the
   match.  In OCaml that is merely ugly; in C it is worse, because karamel
   compiles a match to a chain of tag tests and has to close it with an
   `KRML_HOST_EPRINTF("unreachable (pattern matches are exhaustive in F*)")`
   default.  Recognizing the two-branch boolean shape removed half of those
   from the Pulse hash table and 10% of its C.

   The catch-all side may be `PWild`, `PVar` (F\* names the scrutinee even
   when the name is unused -- if it *is* used the match stays, since there
   would be nothing to bind it to) or the complementary literal.  The first
   branch has to be a literal: two catch-alls are no evidence that the
   scrutinee is a boolean at all.  What remains after this are matches on real
   datatypes, and there karamel emits the same unreachable default for the ML
   pipeline as it does for Custard.

6. **Dead-code elimination**: reachability from the declarations flagged
   `Root`/`Entrypoint`, following the names in bodies, binder types, result
   types and field types (a constructor name resolves to its `DType`).  The
   pass runs *after* inlining, when the call graph is final, and its job is to
   collect what inlining orphaned: a projector or an `external` alias that was
   substituted into every use site is still a declaration until something
   deletes it.

   It is deliberately *not* the mechanism that keeps ghost code out — see
   §5.1's "erase on sight" rule.  It once was, and that was a mistake: a
   request is a side effect, so by the time the simplifier deleted a reference
   to `Ghost.hide`, the transitive closure of its argument — `mk_init_pht`,
   `Seq.create`, `FStar.SizeT.v`, `Prims.op_Subtraction` — had already been
   specialized and emitted.  Deleting it afterwards happened to work, but it
   meant Custard was paying to extract, monomorphize and simplify the entire
   specification of every data structure it touched, and any error raised while
   doing so (a `Mono` binder in ghost code, say) was a spurious failure about
   code that was never going to be emitted.
7. **Representation rewriting** (`Simplify.inline_fields` and
   `Simplify.records`), which apply the §5.5 and §5.7 verdicts and decide
   nothing; see §5.5's "where the decision lives".

   There used to be an **unused-parameter elimination** here
   (`Simplify.unused_params`), the analogue of
   `src/extraction/FStarC.Extraction.ML.RemoveUnusedParameters.fst`: a
   least-fixpoint scan over the whole program for type parameters that no
   field mentions, followed by dropping them and their arguments at every use
   site.  It is gone.  A phantom parameter costs nothing in OCaml, where the
   parameter is only a name, and is gone before either C backend sees anything,
   since monomorphization has run; and being a whole-program decision about a
   type's *arity* it was exactly the sort of thing §5.5's principle forbids —
   the one decision left that a separately compiled unit could not reproduce.
   An author who wants a phantom parameter to cost nothing can wrap it in
   `erased`, which §5.1 removes for reasons that are local to the type.
8. **SCC computation and topological sort** of the final decl list
   (`Simplify.scc`, Tarjan).  The extraction loop appends a declaration once it
   has finished translating it, so everything a definition mentions precedes
   it — a topological order, but only while the dependency graph is acyclic.
   Recursion is exactly the case where no such order exists, and both targets
   want a cycle written as one group.  The pass finds the cycles, orders the
   components dependencies-first, makes the members of a component adjacent
   (ordered among themselves by their previous position, so the output is
   stable), and tags each member with `Rec` naming the whole component.

   The pass is also what makes `Rec` mean what §`Syntax` says it means — "the
   SCC this declaration belongs to" — rather than what the source said.
   `extract_lid` can only set it from F\*'s `is_rec`, which the passes above
   invalidate in *both* directions: unrolling a recursive definition against a
   `Mono` argument leaves a body with no self-call (`Unroll` is exactly this),
   and inlining can introduce a call that closes a cycle.  So `scc` clears any
   inherited `Rec` and recomputes.  A single-member component is recursive only
   if it really does refer to itself.

   A component never mixes `DType`s and `DLet`s, because a type cannot mention
   a value.  The OCaml backend joins the members of a component with `and`
   (writing `let rec`/`type` only on the first); the C backend needs no
   grouping, since karamel recovers recursion itself.

   The OCaml backend has one rewrite of its own here, because OCaml is missing
   a pattern form the IR has: there is no integer *pattern*.  `Prims.int` is a
   `Z.t`, whose literals are calls to `Prims.parse_int`, and a machine integer
   literal is a call to `uint_to_t`; neither is a pattern.  So `PConst (CInt
   _)` is printed as a fresh variable plus an equality in the branch's `when`
   clause -- which is what the ML extraction does too.  The C backend has real
   integer patterns and keeps the `PConst`; it is also the backend that
   rejects guards, which is why this cannot be a shared pass.

9. **Renaming** (`FStarC.Custard.Rename`): give every bound name its source
   spelling back.

   Extraction names a local after the F\* `bv` it came from, because two
   distinct `bv`s routinely share a `ppname` and the IR has no binding
   structure of its own to disambiguate them.  The obvious encoding —
   `ppname ^ "_" ^ index` — is a disaster for reviewability: `bv` indices come
   from a global counter, so touching *anything* upstream renumbers every local
   in the program and the diff is unreadable.  Since the generated code is
   meant to be read and checked in, that matters.

   So the uniquifying suffix is written with `Syntax.uniq`, which separates it
   with a `#`.  No F\* identifier and no target-language identifier can contain
   one, so `Syntax.base_name` recovers the original spelling exactly, and a
   name that escaped this pass is obvious on sight (the printers sanitize it to
   `_` rather than emit it).  Everything that invents a name goes through
   `uniq`: `Extract.name_of_bv`, the eta-expansion binders of a builtin rule,
   `Simplify.rename` for the inliner's capture avoidance, and `Layout`'s
   placeholders for dropped fields.

   The pass then walks the program with a scope, renaming each binder to its
   bare `base_name` and appending `1`, `2`, … only when that would actually
   shadow something already in scope.  Three namespaces are handled
   separately, because they do not interfere: locals (per enclosing term), type
   variables (per declaration), and record/variant fields (per constructor,
   with the result published so that `EProj`/`ERecord` elsewhere agree).
   `uu____NNN`, which F\* invents for a binder written `_`, is collapsed to
   `tmp` — its digits are exactly as volatile as the suffix being removed.

   It runs last, after every pass that might invent a name, so what a reader
   sees is stable under everything that happened before it.

Emission:

- **Krml** (implemented, M5b): `FStarC.Custard.PrintKrml` targets the same
  karamel AST as `src/extraction/FStarC.Extraction.Krml.fst`, writing the same
  `(version, files)` binary via `save_value_to_file` (cf.
  `Universal.fst:408`).  This is the first backend to build, because it gets us
  end-to-end C output with no new code generator.  Karamel's own
  monomorphization then has nothing left to do.  Select it with
  `--custard_backend Krml` (the default is `OCaml`); the output file defaults
  to `Custard.krml`.

  To make the AST shareable, it was moved verbatim out of
  `FStarC.Extraction.Krml.fst` into a new `FStarC.Extraction.KrmlAst.fst`,
  which `Krml.fsti` re-exports with `include` so that every existing client
  keeps compiling unchanged.

  Three points of the translation are worth recording.  *First*, Custard's
  mangled name goes in the identifier but the **namespace stays the F* one**
  (`lident_of_name`), because karamel recognizes its own builtins — `Prims.*`,
  `FStar.UInt32.*`, the Pulse primitives — by fully qualified name; karamel
  joins the two with `_` for the C name anyway, so nothing is lost.  For the
  same reason, the types karamel knows natively (`Prims.unit/bool/int/string`)
  are mapped to `TUnit`/`TBool`/`TInt CInt`/… and their `DType` declarations
  are **skipped**, rather than redeclared.  Also by name: `Prims.op_Equality`
  and `op_disEquality` are operators, not calls — left as externals they get a
  `void *` C signature that no `eqtype` fits.  karamel types decidable equality
  only through an explicit type application naming the operand type
  (`Checker.infer`, the `ETApp (EOp (Eq|Neq), _)` case), so Custard emits
  `EApp (ETypApp (EOp (Eq, Bool), [t]), args)`, `t` being the type of the first
  operand.

  Getting a real program through karamel also depends on Custard's types being
  real.  `ECons` carries the type of the value being built and `EFlat`/`EField`
  the type of the record, and karamel's datatype passes call `assert_tlid` on
  them: an `any` there is a hard error, not a fallback.  So a constructor
  application takes its type from the constructor's result type with the
  inductive's parameters instantiated from the spine, and a call takes its type
  from the callee's already-emitted signature, instantiated at the call's type
  arguments (requests are depth-first, so it is available; a recursive call
  falls back to `TAny`).  Two consequences worth stating: a `DExternal` has no
  type-parameter list in karamel's AST, so a free type variable in its
  signature is printed as `TAny` rather than reported as unbound; and
  `U.abs_formals` opens a definition's binders under fresh names while the
  computation type still speaks of the ones `specialize` abstracted over, so
  the two have to be related by an explicit substitution or the result type
  mentions type variables that no binder introduces.  *Second*, `EDiscrim` has no karamel
  counterpart and is compiled to a two-branch match (karamel has no wildcard
  pattern, so the default branch binds a fresh `PVar`); this needs constructor
  arities, hence the small `ctor_arity` table built up front.  *Third*, the
  constructs C cannot express — `POr`, pattern guards, character constants,
  `ERaise`/`ETry`, `DExn` — become `EAbortS` or a warning, not a crash.

  This backend is also what forced the `Prims` boolean connectives into the
  rule table of §8.2: emitted as ordinary calls they become a `DExternal`
  `Prims_op_AmpAmp`, which nothing defines.  The `Prims` *comparison and
  arithmetic* operators are deliberately left alone, because they act on
  unbounded integers that no C backend can represent, and a link error naming
  `Prims_op_LessThan` is a better diagnostic than silently truncating.
- **ML/OCaml**: `FStarC.Custard.PrintOCaml` prints OCaml source directly.
  Every top-level declaration carries its type — each binder and the result —
  because Custard knows all of them exactly, and writing them down turns a
  mistake in the extraction into an OCaml type error at the declaration rather
  than a puzzle at some use site much later.

  A `DExternal` produces no declaration at all: it is a reference to a
  hand-written realization (`FStar_IO.print_string`), so it is printed at each
  of its uses.  Binding it to a local alias first would only add a layer of
  names to see through.

  The design sketch below predates the printer and is kept for the
  alternative it describes: `FStarC.Custard.ToML` would produce the existing
  `mlmodule` and
  reuses `FStarC.Extraction.ML.Code`'s printer.  Note the impedance mismatch:
  Custard's collapsed representations are *not* well-typed OCaml in general
  (that is why `MLE_Coerce`/`Obj.magic` exists), so `ToML` re-inserts
  `Obj.magic` where a collapse crossed a type boundary.  This is fine — it is
  exactly what the current extraction does, just less often.

  *Polymorphic recursion* is best-effort.  Because every emitted `DLet` carries
  an explicit type scheme (§2.2) and the ML printer emits a top-level
  annotation, OCaml's `let rec f : 'a. 'a t -> int` form should accept it, and
  the residual polymorphic decls after monomorphization are few.  It is not a
  priority: if it does not typecheck, falling back to `TAny` (`Obj.t`) at the
  offending parameter is an acceptable answer.
- **C directly**: `FStarC.Custard.PrintC` (`--custard_backend C`) prints C11
  source with no runtime of its own — the only headers are `<stdint.h>`,
  `<stdlib.h>`, `<stdbool.h>` and `<string.h>`, and the only definition the
  backend contributes is `typedef uint8_t custard_unit;`.  No krmllib, no
  macros: a generated file is meant to be readable, and to be compilable by
  any C11 compiler with nothing installed.  "Pretty C" is still a non-goal;
  *warning-free* C is not, and the corpus compiles with `-Wall -Wextra
  -Werror`.

  This is the backend that has the least to work with, so it is the one that
  most depends on the earlier phases.  It **requires
  `--custard_monomorphize_types true`** (§5.0.1) — C has no type variables,
  and there is no `Obj.t` to hide behind — and it leans on ANF for evaluation
  order and on the `Layout` fixpoint for the shape of every value.

  **Expressions become statements.**  C's expression language is much smaller
  than the IR's, so the printer is two mutually recursive functions rather
  than one:

  - `emit ind dest e` compiles `e` into a *statement sequence* that delivers
    its value to `dest`, which is either "return it", "assign it to `x`", or
    "discard it".  `ELet`, `EMatch`, `EIf`, `ESeq`, `EWhile`, `EAbort` and the
    buffer primitives of §7.4 are compiled here.
  - `c_expr out ind e` prints `e` as a C *expression*, appending to `out` any
    statements that had to be hoisted first.  A subterm that only `emit` can
    handle is hoisted into a fresh temporary.

  ANF has already made most operands atomic, so hoisting fires rarely; keeping
  it is what makes the printer total rather than a source of "this shape cannot
  appear here" failures.

  **Layout choices.**  A record becomes a `struct`; a variant whose
  constructors are all nullary becomes an `enum`; a **single**-constructor
  variant becomes a plain `struct` with no tag and no union, which is what
  keeps tuples and Pulse's one-constructor records free.  Anything else is a
  tagged union.  Constructor applications are C99 compound literals with
  designated initializers, so a value is built in one expression and the
  printer never has to name a partially initialized object.

  **Matching is an if/else-if chain**, not a `switch`: nested patterns,
  constant patterns and variable patterns then all go through one mechanism,
  which walks a pattern against an access *path* and returns a list of tests
  and a list of bindings.

  Three things the chain deliberately does *not* do:

  - It does not test the **last** branch.  F\* has already checked that the
    match is exhaustive, so the last arm is the one that runs when no earlier
    one did; testing it anyway would only add an `else { abort(); }` that C
    cannot see is dead.  This is the same reasoning that lets `EProj` be
    emitted without a tag check.  An `abort()` in the output therefore always
    stands for something in the source — a `Pulse.Lib.Dv.unreachable`, a failed
    allocation — and never for the backend hedging.
  - It never sees a branch that only **aborts**: §5.6 has already dropped
    those.  That is what lets the branch before such a one become the
    unconditional one here.
  - It does not **copy** what a pattern binds.  A binding names a value that is
    already reachable as a projection out of the scrutinee, and both are
    immutable, so the variable is bound to the *path* rather than declared:
    `{ size_t sz_1 = s.sz; t = sz_1; }` becomes `t = s.sz;`.

  **A definition returning `unit` returns `void`**, and a `unit` binding is an
  alias for the constant rather than a variable.  Nothing follows a value's
  destination — every construct hands it to its tail positions and emits no
  statement after them — so in a `void` function the value is dropped and
  control falls off the end, which is where it was going anyway.  At a call
  site a `void` call is a statement, so it is emitted as one and stands for
  the unit value.

  **Braces are only written where they hold something.**  A single-statement
  `if` or `else` body is written inline, which the printer can decide safely
  because it emits one statement per line and anything that could dangle
  spans more than one; and the arm of a match that runs when no earlier one
  did is emitted flat when there is no `if` before it, rather than wrapping
  the rest of the function in a block that says nothing.

  **`let mut` becomes a local variable.**  Pulse compiles a `let mut` to a
  stack allocation of one cell (§7.4), and a one-cell array *is* a variable:
  reads and writes of the cell become uses and assignments of it, and the uses
  that want a pointer — passing it to a function expecting a `ref` — take its
  address, which is what a C programmer would have written.  The Pulse checker
  has already established that the cell does not outlive its scope, so the
  address is never stale, and the matching "free" Pulse emits for a stack
  allocation is scope exit, so it emits nothing.  This removes a declaration,
  an array and an initializing loop per mutable variable.

  **No variable that only renames another.**  Four places used to introduce
  one, and each is removed by a condition the backend can check locally:

  - The **scrutinee** of a match is normally named, because it is read once per
    test and once per binding — but when it is already a name, or a projection
    out of one, it is used directly.  The backend never assigns to such a
    variable, which is what makes that safe.
  - A **read of a `let mut` cell** binds a copy, which is what makes the rest
    of the term see the value it started with.  When nothing in that rest
    writes the cell or takes its address, there is nothing to be protected
    from, and the binding becomes another name for the cell.  Where a write
    *does* follow — the loop counter Pulse increments at the end of an
    iteration — the copy stays.
  - A **hoisted temporary** whose statements came out as a single assignment to
    it was only ever going to hold that right-hand side, so the right-hand side
    is used instead.  This needs the hoisted expression to be *pure*, since it
    moves; it is what turns a record projection — which reaches the backend as
    a one-branch match — back into the projection it was.
  - A **declaration and its only assignment**, next to each other, are one
    definition.  Nothing moves here, so this one needs no side condition.

  **A `unit` parameter the body never mentions is dropped**, from the
  signature and from every call site — it is how F\* writes a thunk, and C has
  no laziness to preserve.  So `main` is `int32_t main(void)`, not
  `int32_t main(custard_unit tmp)`.  ANF is what makes dropping the *argument*
  safe: every operand is already pure, so not evaluating it loses nothing.

  **C scoping is coarser than the IR's.**  A chain of `ELet`s, and a loop's
  condition and body, all land in the same C block, while the IR scopes them
  separately — so two disjoint IR scopes can collide on a name.  The printer
  therefore tracks, per function, which names it has already emitted, and
  appends `_1`, `_2`, … only on a real collision.  The common case keeps the
  name the F\* programmer wrote.

  **Function pointers, but not closures.**  A `TArrow` in a value position is
  a C function pointer: `size_t (*hashf)(size_t)`.  That is enough for the
  Pulse hash table, whose `ht_t` record stores its hash function, because
  Custard has no closures left by this point — the value is always a top-level
  definition, whose name *is* the pointer.  A surviving `EFun` (a lambda that
  captures) is rejected.

  Building the type and the name together, from the inside out, is what a C
  declarator requires, and doing it once (`decl_of t x`, with `x = ""` giving
  the abstract declarator a cast wants) is what keeps returned pointers
  (`uint32_t *f(void)`) and stored functions correct without a special case at
  each use.

  **What it rejects, and why each is a rejection rather than a fallback.**
  Every one of these is a case where C *could* be emitted, but only by
  guessing; error 367 names the enclosing declaration and says what to do.

  | Rejected | Why |
  |---|---|
  | `TVar`, polymorphic `TApp` | no type variables in C; run with `--custard_monomorphize_types true` |
  | `EFun` in a value position | no closures; mark the parameter `[@@@monomorphize]` (§3.1) |
  | abstract types, `Prims.int` in particular | no size, and no width to guess |
  | unbounded integer literals | same |
  | `TAny` | the representation was already lost; `--custard_warn_any` (§5.9) says where |
  | `TTuple`, `ETuple`, `PTuple` | tuples must have reached the backend as `tupleN` inductives |
  | `POr`, pattern guards | no `EAbortS`-style approximation is available here |
  | `ERaise`, `ETry`, `DExn`, `TExn` | no exceptions (§8.5) |
  | recursive datatypes | a C struct cannot contain itself by value |
  | a top-level `DLet` with no binders | C cannot initialize a global from a computation |

  Compare the Krml backend, which *approximates* several of these (`EAbortS`,
  a warning) because krml has a runtime and a monomorphizer of its own to fall
  back on.  This backend has neither, so an approximation would only move the
  failure to the C compiler, with a worse message.

  **Entry points.**  An entry point returning a machine integer becomes
  `int main(void) { return (int)f(...); }` — the process exit status; anything
  else is run for its effect and `main` returns 0.

  Tested by `tests/custard/KrmlBasic.fst` (records, variants, machine
  integers, casts, mutual recursion, short-circuiting) and by both Pulse
  modules, each compiled with `-Werror` and run;
  `tests/custard/CNoInt.fst` and `CNoClosure.fst` are the negative tests.

---

## 7. Effects and purity

The custom-rule table of §8 is a *value*-level mechanism: it says what a call
translates to.  That is not enough for effects, because an effect changes what
transformations are legal on the surrounding code — a call in an impure effect
may not be dropped, duplicated, or reordered with another effectful call.  So
effects get their own phase, running before the phase-4 rewrites, and every
rewrite in phases 4–5 is guarded by it.

### 7.1 The effect lattice

Custard's `eff` (§2.2) is a three-point lattice:

```
  E_Ghost  <  E_Pure  <  E_Impure
```

- `E_Ghost` — computationally irrelevant.  Erased entirely (§5.1).
- `E_Pure` — total and effect-free.  Freely droppable, duplicable, reorderable.
- `E_Impure` — anything else: divergence, state, exceptions, IO, concurrency.
  Neither droppable, duplicable, nor reorderable.

We deliberately do *not* subdivide `E_Impure` (no separate `Div` vs `ST`).
Custard performs no effect-directed optimizations beyond the drop/dup/reorder
question, and for that question all impure effects behave identically.  (This
matches `e_tag` in the ML extraction, `Syntax.fsti:50`.)

Every source computation type is mapped into this lattice by
`FStarC.Custard.Effects.classify : TcEnv.env -> comp -> eff`:

| Source | `eff` |
| --- | --- |
| `Tot`, `Pure`, `Lemma`-free pure code | `E_Pure` |
| `GTot`, `Ghost`, anything `non_informative` | `E_Ghost` |
| `Div`, `Dv`, `ML`, `ST`, `Ex`, … | `E_Impure` |
| a user effect with `Extract_reify` | `E_Impure` (see below) |
| a user effect with `Extract_primitive` | `E_Impure` (see §7.2) |
| a user effect with `Extract_none` | hard error, if reachable (code 365) |

`Extract_reify` and `Extract_primitive` are not distinguished here.  Reification
(§7.5) changes the *term* Custard extracts, and the type it gets, but not the
drop/duplicate/reorder question, which is all `eff` is used for.  In fact after
reification the reifiable effect has disappeared from the computation type
entirely and what is left is the effect of the representation — `Dv` for `Tac`
— so the row above describes a comp Custard only sees on its way past it.

The three-way distinction comes from `TcUtil.effect_extraction_mode`
(`src/typechecker/FStarC.TypeChecker.Util.fst:3288`, returning
`eff_extraction_mode` from `src/syntax/FStarC.Syntax.Syntax.fsti:605`), which
the ML extraction already consults at `Term.fst:658` and `Modul.fst:869`.

### 7.2 `extract_as_impure_effect`

Pulse's `stt`/`stt_div`/`stt_atomic` are *not* F* effects at extraction time —
they are ordinary type constructors carrying the
`[@@extract_as_impure_effect]` attribute
(`ulib/FStar.Attributes.fsti:366`, lid
`Const.extract_as_impure_effect_lid` at `src/parser/FStarC.Parser.Const.fst:534`).
The attribute's contract, from its own documentation, is:

> if you have `[@@extract_as_impure_effect] val stt (a:Type) (pre:_)
> (post:_) : Type` then arrows of the form `a -> stt b p q` will be extracted
> similarly to `a -> Dv b`.

The ML extraction implements this in `Term.fst`:
`has_extract_as_impure_effect` (`:676`) tests the attribute;
`head_of_type_is_extract_as_impure_effect` (`:679`) tests it on the head of a
codomain; `fv_app_as_mlty` (`:719`) drops the marker and translates the *first*
type argument as the result type; and the `Tm_arrow` case (`:776`) promotes the
arrow's `etag` to `E_IMPURE` when the codomain's head has the attribute.

Custard needs the same three behaviours, and they are all *type*-level, which is
why §8's expression-level rules cannot express them:

1. **Result-type projection.**  `stt b p q` has representation `b`.  This is
   really a layout rule: `TApp (stt, [b; p; q])` ⟹ the layout of `b`, with the
   index arguments `p`/`q` erased.  It composes with §5 — if `b` is itself a
   newtype, the result is the collapsed payload.
2. **Effect promotion.**  `a -> stt b p q` classifies as
   `TArrow (a, E_Impure, b)`.  Crucially the promotion happens on the *arrow*,
   so it is visible at every call site of every function of that type,
   including one reached through a `Poly` binder.
3. **Purity discipline** on the resulting `E_Impure` nodes — §7.3.

The check is a single attribute lookup on the head fv
(`TcEnv.fv_has_attr env fv Const.extract_as_impure_effect_lid`), so this is
cheap and can be done during type translation, exactly as the ML pipeline does.
All three live in `FStarC.Custard.Effects`: `of_lid` is the §7.1 table,
`impure_effect_result` is the result-type projection, and `of_comp` is the
effect *including* the promotion, so that the extractor cannot accidentally
consult one without the other.
Note it must be applied to the head of the *codomain* after normalization, not
just to syntactic occurrences, since `stt` is often behind an abbreviation.

The generalization worth keeping in mind: an effect in Custard is a property of
an *arrow type*, computed from the codomain, not a property of a `let`.  That
is what makes it work for Pulse, where the effect is encoded in a type.

### 7.3 The purity discipline

Every phase-4/5 rewrite that removes, duplicates or moves a subterm must
consult `eff`:

| Rewrite | Guard |
| --- | --- |
| drop an unused `ELet` (§6, pass 4) | body's `eff ≤ E_Pure` |
| drop an erased field/argument (§5.1) | argument's `eff ≤ E_Pure`, else hoist |
| drop the non-surviving args of a collapsed ctor (§5.2) | same |
| drop a redundant `ECast` (§5.4) | always legal — `ECast` is pure |
| inline a `let x = e in C[x]` with one use | `e.eff ≤ E_Pure`, or the single use is in evaluation position and no impure computation is crossed |
| duplicate a subterm (e.g. into two match branches) | `eff ≤ E_Pure` |
| reorder two subterms | at most one is `E_Impure` |
| DCE a whole top-level `DLet` | its `eff ≤ E_Pure`.  An effectful one is a module initializer and is a root of the extraction (§4.4) |

"Hoist" means: replace the dropped argument `e` by an enclosing
`ELet (x, e.ty, e, ...)` so its effect still happens, in the right order, even
though its value is unused.  This is what makes erasing an argument of an
`E_Impure` call sound.

There is a third source of effect information besides declarations and
computation types, and it is easy to miss: a call through a *variable* --- a
function parameter, or a local closure --- has no declaration to consult.  Its
effect has to come from the arrow type of the head, by joining the effects of
the arrows the application consumes (`Extract.apply_eff`).  When the head's
type is not arrow-shaped (typically `TAny`) the answer must be `E_Impure`, or
the table above would happily delete a call we know nothing about.  For the
same reason a lambda is given a proper arrow type rather than `TAny`.

Dually, a *partially* applied callee is a closure, and building a closure is
pure however impure calling it will be; `Extract.callee_eff` therefore compares
the number of supplied arguments against the callee's arity.  "Arity" here
means the number of *lambdas* the definition actually has, not the number of
arrows in its type, and the difference matters for a definition such as

```fstar
let step (n:int) : ML (int -> Tot int) = print_string "step "; (fun y -> y + n)
```

whose effect fires after *one* argument.  Because `dl_binders` comes from the
definition's lambdas, `step 1` counts as saturated and is correctly impure.
The converse case, where the definition has more lambdas than the type has
arrows before its effect — `let mk (n:int) : ML (int -> Tot int) = fun y -> y + n`
— is sound for a subtler reason: for the surplus binders to exist, the effectful
computation has to be syntactically a lambda, i.e. a value, and so has no
effects to lose.

ANF is what makes this tractable, which is why it is phase 4's *first* pass
(§6): after ANF every impure computation is a named `ELet` in a fixed order, so
"reordering" is a question about statement order rather than about arbitrary
subterm positions, and every rewrite in the table above then operates on pure
operands only.

One more thing this table depends on, and it is easy to get wrong in the
conservative direction: an **external**'s effect is `apply_eff` of its declared
arrow type, not `E_Impure`.  A hand-realized symbol's F\* type is the whole
contract we have with its realization — it is the same contract the ML pipeline
and karamel work from — and almost all of them are `Tot`.  Answering
`E_Impure` for every external instead puts a barrier around `Prims.op_Addition`
and every other arithmetic primitive, `Prims.strcat`, `string_of_int` and the
`to_string` of every machine integer, which then blocks inlining, blocks iota
through `ctor_args_pure`, and makes ANF name a temporary for each of them.
`apply_eff` still answers `E_Impure` when the type is not an arrow, so a symbol
we genuinely know nothing about (`dx_ty = TAny`) stays opaque.

### 7.4 Statement-shaped effectful primitives

Pulse's `while` and its reference/array operations are impure *and*
statement-shaped: the C backend needs their block structure, not a call.  These
get a **fixed set of IR nodes** (`EWhile of expr & expr`, and the reference and
array operations as `EOp`s), rather than an extensible `EOp` carrying blocks.
The fixed set is simpler, Pulse is the only client today, and an extensible
block-carrying node can be added later without disturbing anything else.

One caveat, and it constrains the IR: **we should not assume we can recover a
scoped `EWithLocal`.**  Pulse emits stack allocation as *separate* alloc and
"free" operations, not as a bracketing construct, so the natural IR is two
independent impure operations:

```
  let r = EOp (Alloc, [init]) in   ...   ; EOp (Free, [r])
```

Reconstructing a scoped `with_local r init { body }` from that pair means
proving the free dominates every use and matches the alloc — recoverable in
easy cases, not in general.  So:

- the IR has `Alloc`/`Free` as ordinary impure operations, and a scoped
  `EWithLocal` is at most an *optional* node produced by a recovery pass, never
  something the frontend is required to produce;
- the C backend must be able to emit the unscoped form (a C block-scoped
  variable when recovery succeeds, otherwise whatever karamel does today for
  the same pattern);
- the purity discipline (§7.3) is what keeps this correct in the meantime:
  `Alloc`/`Free` are `E_Impure`, so no pass may drop, duplicate or reorder them
  past each other.

Recovering scopes is a C-quality optimization, and "pretty C" is an explicit
non-goal, so it is firmly optional.

### 7.5 Reification

An effect whose `effect_extraction_mode` is `Extract_reify` is not compiled as
an effect at all.  It is compiled through its **representation type**, and the
only effect that survives into the IR is the one the representation itself
carries.  ulib's `Tac` is the case that matters:

```
  let tac_repr (a:Type) (wp:tac_wp_t a) = ref_proofstate -> Dv a
```

so a metaprogram

```
  val mk_class : string -> Tac (list sigelt)
```

is compiled as

```
  mk_class : string -> (ref_proofstate -> list sigelt)
```

— a *pure* function of the string, returning a closure that expects the
proofstate, whose application is impure.  Note where the effect went: applying
`mk_class` to its own argument builds a closure and runs nothing, so the arrow
that returns the representation is `E_Pure`, and the `E_Impure` reappears on
the representation's own arrow, which `ty_of_typ` reads off it like any other.

This is not a matter of taste.  Compiling the effect away instead — giving
`mk_class : string -> list sigelt` — leaves the proofstate nowhere, and the
proofstate is not an implementation detail of the tactic engine: it *is* the
tactic engine's state, threaded explicitly because a metaprogram may fail, be
backtracked, or be resumed.  Worse, it would leave the two halves of the
compiler disagreeing.  `FStarC.Tactics.Monad.tac r`, which is an ordinary type
abbreviation and which Custard already compiles correctly as `proofstate ref ->
r`, is *the same type* as `tac_repr r wp`; every hand-written realization under
`ulib/ml/plugin` has it in its signature, and so does every
`mk_tactic_interpretation_N` a plugin registration goes through.  A Custard that
did not reify could not link a tactic against the engine that runs it.

Three places implement it, mirroring the ML pipeline
(`FStarC.Extraction.ML.Term.fst:656`):

- **Types.**  `ty_of_typ`'s `Tm_arrow` case asks `Effects.is_reifiable` about
  the codomain's effect, and if so replaces the codomain by
  `Effects.reify_comp` — `TcEnv.reify_comp env c U_unknown` — and marks the
  arrow `E_Pure`.
- **Terms.**  `expr_of_term`'s `Tm_abs` case, and `extract_letbinding` for a
  definition's body, wrap the body in `reify` against the residual effect the
  binders were opened with, and normalize with `TcUtil.norm_reify`.  That
  reduction has to finish the job: `reify e` is only a marker, and what makes
  the result a term of the representation type is unfolding the effect's `bind`
  and `return`.
- **Leftovers.**  A `reify` written by hand — the tactic library does — arrives
  as `Tm_constant (Const_reify (Some l))` at the head of an application, and is
  performed on the spot in `expr_of_term`'s `Tm_app` case.  It is not a
  function and has no value of its own, so leaving it alone would emit an
  application of `()`.

The reification is deliberately *not* folded into `custard_norm_steps`.  A
`reify` has to be introduced against the effect that a particular term is known
to have, which is a piece of information the normalizer does not carry, and
enabling `Reify` globally would only unfold the `reify`s that were already
there.

`tests/custard/Reify.fst` pins the shape of the output.

---

## 8. Custom extraction rules

We currently have various extraction rules for external operations.  Notable
examples:

 - Pulse: stack-allocated variables, while loops, reference/array ops
 - Machine integers

In the current ML extraction pipeline, these are replaced by IR operations in
the extraction pass to karamel, customizable by plugins.  For OCaml extraction,
we add implementations for these functions in .ml files.

At first, it's fine to hardcode all of these.

### 8.1 What the mechanism has to cover

Concretely, the rules fall into four kinds:

1. **Primitive operations**: `UInt32.add`, `UInt32.logand`, … map to `EOp`
   nodes with a target-specific meaning.  In the ML pipeline these are matched
   by name in `FStarC.Extraction.Krml.fst`'s `translate_expr`.
2. **Primitive types**: `UInt32.t` ↦ a machine type.  `Krml.translate_type`.
3. **Statement-like constructs**: Pulse's `while`, `with_local`, `ref` ops.
   These need to survive as IR nodes rather than as calls, because the C
   backend needs their block structure.  They are also *effectful*, so the
   rule table alone is not enough — see §7.4.
4. **Hand-realized definitions**: `assume val`s implemented in an `.ml`/`.c`
   file.  These become `DExternal` plus a link-time obligation.
5. **Width conversions**: `FStar.Int.Cast` and `FStar.SizeT`'s
   `uintN_to_sizet` family map to the IR's single coercion node, `ECast`.

Kind 5 is the one where the two backends visibly disagree, and it is worth
recording why.  `uint32_to_uint8` is *specified* as `v x % pow2 8`, and the
signed conversions as `v x @% pow2 n`; that is exactly what a C cast does, so
the Krml backend emits `(uint8_t)x` and is done.  Compiling F\*'s own
definitions instead would be correct but drags `Prims.pow2` — a recursive
function over unbounded integers — into the program, and krmllib does not
help: it ships an `FStar_Int_Cast.h` full of `extern` declarations and *no*
implementation, precisely because the reference pipeline reduces these to
casts long before they reach C.

OCaml cannot do the same, because every machine width there is a *distinct*
type: `Stdint.UintN.t` at most widths, plain `int` for `FStar.UInt8`, and a
boxed `Sz of UInt64.t` for `FStar.SizeT`.  An `Obj.magic` between two of them
is a miscompilation, not a no-op, and a narrowing conversion additionally has
to do the masking that the C cast does implicitly.  So the OCaml backend
prints an `ECast` between two machine widths as the corresponding
`FStar_Int_Cast` function, which `ulib/ml` realizes and which is by
construction the same specification.  `FStar.SizeT` is not in that module, but
its conversions are exact by their own preconditions, so they go through
`Prims.int` — `FStar_SizeT.uint_to_t (FStar_UInt16.v x)` — the way the
realization itself does.

`tests/custard/MachineInts.fst` covers widening, unsigned narrowing, signed
narrowing and the `FStar.SizeT` round trip on the OCaml side, and
`tests/custard/KrmlBasic.fst` covers them on the C side.

Effect-level behaviour (`extract_as_impure_effect`, effect classification, the
drop/dup/reorder discipline) is deliberately *not* part of this table; it lives
in §7, because it constrains the surrounding code rather than translating a
call.

### 8.2 Design

A single table, consulted in step 1 of the extraction loop, *before* the
definition is looked up, so that a definition with a rule is never requested
and never appears in the output.  This is `FStarC.Custard.Builtins`:

```fstar
type rule =
  | Rule_prim   of int & (list cty -> list expr -> ML expr)  // build EOp/ECtor/...
  | Rule_type   of (list cty -> ML cty)
  | Rule_extern of { x_name: option string; x_header: option string }
  | Rule_opaque                                              // fix the representation
  | Rule_realized                                            // the module is hand-written OCaml

val register_rule : lid -> rule -> ML unit
val lookup_rule   : lid -> ML (option rule)
```

The `int` in `Rule_prim` is the arity: a primitive is an *operator* in the IR
but a *function* in F*, so a use that supplies fewer arguments than the rule
needs is eta-expanded rather than rejected.  This is what lets a primitive
still be passed as an argument (`twice UInt32.add_mod x`).

`Rule_extern` is how a definition whose F* "body" is a specification — often
literally `admit ()`, as for `UInt32.to_string` — becomes a `DExternal`, whose
OCaml realization is the existing `FStar_UInt32.to_string`.

Phase 1, which is what is implemented, hardcodes the rules.  Machine integers
are matched by the *shape* of the name rather than enumerated: the module name
gives the width (`FStar.UInt32` ⟹ `(Unsigned, Int32)`) and the identifier gives
the operator, following `FStarC.Extraction.Krml`'s `mk_width` and `mk_op`
exactly — karamel is the backend that has to give these a C meaning, and a
discrepancy there would be a miscompilation rather than an error.  The IR gains
a `TInt of signedness & width` type and a structured `prim_op` for this.

`FStar.Ghost` is not in the table: it is handled by erasure (§5.1).
`FStar.Pervasives.Native` is, but as a *realized module* rather than as a
family of rules; see below.  The
`Prims` boolean connectives (`op_AmpAmp`, `op_BarBar`, `op_Negation`) *are*,
because C has no `Prims_op_AmpAmp` to link against; see §6.

Phase 2 (implemented, M6): the table is registrable from F* plugins, in the
same mutable-ref/registration style already used by
`FStarC.Extraction.Krml.fst` (`ref_translate_type`, `ref_translate_expr`, …)
and `FStarC.Tactics.Native`.  A plugin registers a whole *lookup function*
rather than one name at a time — `register_pre_rule` to run before everything
already registered, `register_post_rule` to run only after they have all
declined — because the interesting rules come in families (every
`FStar.UInt*` operator, every Pulse primitive) that are cheaper to match by
shape than to enumerate.  A lookup declines by raising `No_custard_rule`.
`register_rule` remains as the one-name shorthand.  Pulse can then ship its
rules instead of patching the compiler.

Phase 3 (implemented, M6): the simple rules can be *declared in F* source*, so
that no OCaml plugin is needed for them.

- `[@@custard_extern "target"]` gives `Rule_extern`: the definition is not
  compiled, and uses of it become references to `target` in the output.  An
  empty string means "use the name Custard generated", which is what a
  hand-written `.ml` realization following the usual naming convention wants.
- `[@@custard_c_header "h.h"]` names the C header that declares such a symbol.
  The karamel backend ignores it (karamel takes includes on its command line);
  it is there for the direct-to-C backend of M8.
- `[@@custard_opaque]` gives `Rule_opaque`.
- `[@@@custard_inline_field]`, on a constructor's *binder* rather than on a
  definition, asks for that field to be stored in the constructor itself
  (§5.7).  It is read straight off `binder_attrs` by `Extract`, not through
  `rule_of_attributes`.

These are declared in `FStar.Attributes` and, unlike the table, are found by
*looking at the definition* rather than at its name, so `Extract` consults
`rule_of_attributes` separately — and lets it win over the built-in table, so
that a program can override a rule it does not like.  Note that
`FStarC.Syntax.Util.has_attribute` only matches a bare `fvar`; an attribute
that takes an argument has to be found with `get_attribute`.

Types with custom rules are automatically exempt from erasure and newtype
collapse (§5.2), since their representation is fixed externally.

#### Realized modules

`Rule_extern` names one symbol at a time, which is the right grain for a
definition that F\* declares and OCaml implements.  It is the wrong grain for
the fifty-odd modules of the F\* library and compiler that have a hand-written
`.ml` under `src/ml` or `ulib/ml`.  Those files are not a collection of
individual realizations: each one *is* the module, and the build simply
excludes it from extraction.

The whole-program output has to link against them, and there the difference
between Custard and the ML pipeline bites.  ML extraction emits one OCaml
module per F\* module and never mangles a name, so an extracted
`FStar_Pervasives_Native.option` and a hand-written one are the same type
because they have the same path.  Custard emits *one file*, and its
`fStar_Pervasives_Native_option` is a new type that no realization has ever
heard of.  A realization whose signature mentions an `option`, a tuple, an
`either` or a `range` — which is most of them — then cannot be called at all.

`Rule_realized` says so at the grain that matches: the module.  A type in a
realized module keeps its declaration, so that every pass can still see its
constructors, its fields and their arities, but it is not emitted, and every
reference to it, to its constructors and to its fields prints as the
realization's own unmangled name qualified by the support module —
`FStarC_Platform_Base.sys`, `FStarC_Platform_Base.Win32`.  Its representation
is fixed outside F\*, so `Realized` also implies no erasure, no newtype
collapse and no inline-field expansion; the record recovery of §5.5 still
applies, because F\* and OCaml agree on which declarations are records.

The list of realized modules lives in `Builtins` rather than as an attribute on
each interface.  Fifty attributes would be a fact about the *build* recorded in
the *library*, and would still have to be kept in step with the build; one list
next to the other rules is the same information in one place.  It is the set of
module names for which `src/ml` or `ulib/ml` holds a file of the same name,
plus `FStar.Pervasives`, which is extracted rather than hand-written but whose
`either` and `dtuple` types the realizations use in their own signatures.

**A realization replaces the module, values included.**  Where there is a
hand-written `.ml`, the F\* definitions in the module are a *model*: they are
written to be proved about, they are free to describe a representation the
realization does not use, and where the two disagree the realization is the
one that runs.  Compiling them would be picking silently between two
implementations of the same name.  So a `Sig_let` in a realized module becomes
a `DExternal` naming the realization, and an incomplete realization is a
link error against a realization bug, rather than a program that quietly runs
the model.

`FStar.Dyn` is what makes the disagreement concrete: `dyn` is
`unit -> Dv value_type_bundle` in F\* and `Obj.t` in `FStar_Dyn.ml`, so the
compiled `undyn` forces a thunk that is not one.  But the rule is not about
that module — it is what "the `.ml` *is* the module" means, applied to values.

Three kinds of declaration are not models, and stay compiled:

- a **projector or discriminator**, which is derived from the type declaration
  Custard already has and which §5's inlining turns into the one field read it
  is;
- anything **`inline_for_extraction`**, which in a realized module means
  precisely that the realization does *not* define it — that is what
  `FStarC.PSMap`'s own comment says about its `psmap_*` aliases — so an
  external would be an unresolved symbol;
- a **type abbreviation**, which F\* also represents as a `Sig_let`.  There is
  no such thing as an external type declaration; a realized module's genuine
  types are handled by the `Realized` flag above.

Two modules are listed for their types alone,
`Builtins.type_only_realized_modules`, because their "realization" defines no
representation of its own and so has nothing to replace.  `FStar.Pervasives`
has no hand-written file at all.  `FStar.Pervasives.Native` does, but it is
transparent — `type ('a,'b) tuple2 = 'a * 'b`, and every value a projection out
of it — over types Custard represents natively, so its `fst` and `snd` are
ordinary F\* code over a representation both sides already agree on.
Compiling them is also what keeps `tuple2` monomorphizable: an external's
signature freezes the types in it (§5.0), and a frozen `tuple2` has no C
representation at all.

**An external is instantiated at its call site.**  A realization is written
polymorphically — `let fst = Stdlib.fst` — and taking its declared type at face
value would type every call as returning `any`, which is how one polymorphic
realization poisons every program that touches it.  So `DExternal` carries a
`dx_typars` list beside its type, exactly as a compiled definition carries
`dl_typars`, and §3.2's specialization substitutes the call site's type
arguments into it.  Nothing about the target changes: OCaml's `fst` really is
polymorphic, so naming its result at the instantiation the call site asked for
describes the target more precisely rather than coercing it.  A type parameter
the call site does not supply — an unspecialized `Mono` binder — becomes `any`,
which is what it was before.

**A type can be an entry point.**  A realization does not only *call* into the
extracted code, it names its types, and one kind of name is not there to be
found: Custard unfolds type abbreviations rather than emitting them, because a
monomorphized abbreviation has no generic form left to emit and because the
backends need the representation behind the name (§5.0).  An abbreviation that
only a realization mentions is therefore reached by nothing and dropped as
dead code by §6 pass 6.

`--custard_entry FStarC.Range.Type.t` says otherwise, and there is nothing
special about it: a root is a root whichever kind of declaration it names, and
this is the same idiom §12.9 uses for a realization's callees.  Two things had
to agree with that.  `Extract.run` marks the root, and it used to mark only a
`DLet`, so a type root was emitted and then dropped.  And
`Driver.check_entrypoints` used to reject an entry it could not look up, which
is stricter than the extraction loop: the loop loads a module when it first
reaches one of its definitions (§4.2), so at that point the environment holds
only what the driver happened to load, and loading it early would clash with
the interface the driver already has.  The early check now covers the modules
that *are* loaded, which catches the common case of a typo, and `Extract.run`
reports a root that produced no declaration at all.

What this does *not* buy, and must not, is a representation.  Being an entry
point is a fact about a type's *users*, and §5.5's principle is that a type's
representation is determined by the type alone: a one-constructor type
collapses into its payload whether or not anyone outside names it.  A
realization that spells out such a constructor is written against a
representation that is not there, and it is the realization that has to give
— see §12.10.

**The stub modules are renamed.**  ulib declares the compiler's own
reflection and tactic API a second time, under `FStar.Stubs.*` —
`FStar.Stubs.Syntax.Syntax`, `FStar.Stubs.Tactics.Types`,
`FStar.Stubs.Reflection.Types` and seven more — plus `FStar.NormSteps`.  These
are not separate types: they are `FStarC.Syntax.Syntax`,
`FStarC.Tactics.Types` and so on, seen from user code through an abstract
interface.  A plugin compiled against the ulib names has to
end up calling the compiler's, so the names have to be made to coincide, and
`Builtins.no_fstar_stubs` does it:

```fstar
let no_fstar_stubs (ns : list string) : list string =
  match ns with
  | "FStar" :: "NormSteps" :: rest -> "FStarC" :: "NormSteps" :: rest
  | "FStar" :: "Stubs" :: rest -> "FStarC" :: rest
  | _ -> ns
```

ML extraction has the same rewrite (`UEnv.no_fstar_stubs_ns`) but applies it
only under `--codegen Plugin`, because it also extracts ulib for its own sake,
where the stub names are the right ones.  Custard has no such mode: it compiles
whole programs, and a whole program that reaches
`FStar.Stubs.Tactics.Types.proofstate` is one being linked into the compiler.
So the rewrite is unconditional.

It is applied in `Extract.name_of_lid`, the single funnel from an F\* lid to a
Custard `name`.  Everything downstream — the realization tables,
`Split.file_of`, the unit interfaces of §12, the linker — therefore sees one set of names, and
nothing else in the pipeline has to know that the rewrite happened.  Loading is
still by lid and is untouched.

Three of the rewritten names land on modules that *do* have hand-written
realizations — `FStarC.Reflection.Types`, `FStarC.Tactics.Unseal` and
`FStarC.Tactics.V2.Builtins` — and are listed as realized.  The rest
(`FStarC.Tactics.Types`, `FStarC.Syntax.Syntax`, `FStarC.NormSteps`, …) are
ordinary compiler modules that Custard compiles, and must not be.

#### Types the target already has

`Rule_realized` answers "what does the hand-written file call this?".  For a
few types there is a better answer: **the target has the type already**, and
the realization only says so.  `Prims.list` is `'a list`;
`FStar.Pervasives.Native.tuple2` is `type ('a,'b) tuple2 = 'a * 'b`, an
*alias*; `option` is an alias of the stdlib's.  Naming the OCaml type
directly is therefore not a translation of the realization but the same type
said without the detour — and it is the only spelling that does not require
the realization to be linked at all.

So `builtin_type`/`builtin_ctor` map `option`, `list` and their constructors
to OCaml's own, and `ty` prints `tupleN` in OCaml's tuple syntax.  After that
no Custard-generated line in the extracted compiler names
`FStar_Pervasives_Native`; what is left of that file is there for the ML
extraction, not for Custard.

A tuple stays an ordinary inductive *in the IR* — `PrintC` rejects a bare
`TTuple`, and it is right to: the C backend has no tuple type and §5.6's
field inlining is what gives it a representation.  This is a printing
decision, and only the OCaml printer makes it.  A tuple has no constructor to
name and no field to project, so building one, matching one and reading a
component out of one are all written in OCaml's syntax; a component is read
by a match rather than a projection, since OCaml has none beyond `fst` and
`snd`.  Those two are `inline_for_extraction` in `ulib`, since a call to
either buys an indirection over the field read every backend already emits.

The rule this follows is worth naming, because the tempting generalization is
wrong: **a realized type may be printed as a target type only when the
realization defines it as an alias of that target type.**  `FStar.Dyn`'s
`dyn` is also `Obj.t` in OCaml, but the F\* side is a different type, and
§8.2 already records what happens when a model and a realization are allowed
to disagree.

### 8.3 Pulse

Pulse does not reach Custard as Pulse.  `Pulse.Main.set_impl` attaches an
ordinary F\* `Dv` term to every `fn` as `[@@FStar.ExtractAs.extract_as impl]`,
and the ML pipeline swaps the body in
`FStarC.Extraction.ML.Modul.fixup_sigelt_extract_as`.  Custard does the same,
in `Extract.fixup_extract_as`, at the one point where a `sigelt` is fetched
from the environment; without it a Pulse module extracts to the proof term,
which is nonsense.  The letbinding is re-marked recursive only if the
replacement body actually mentions the name, since Pulse loops are `while_`
applications rather than self-calls.

What is left after that is a handful of primitives, which
`Builtins.pulse_rule` maps to IR nodes, mirroring
`pulse/src/extraction/ExtractPulse.fst`:

| Pulse | IR |
| --- | --- |
| `Reference.ref`, `Box.box` | `TRef t` |
| `Reference.alloc`, `Box.alloc` | `BufCreate LStack` / `BufCreate LHeap` of length 1, at type `TRef t` |
| `Reference.(read, op_Bang, write, op_Colon_Equals)`, `Box.…` | `BufRead` / `BufWrite` at index 0 |
| `Vec.alloc`, `free`, `op_Array_Access`, `op_Array_Assignment` | `BufCreate LHeap`, `BufFree`, `BufRead`, `BufWrite` |
| `Array.Core.*`, `ArrayPtr.*` | the same, plus `BufSub` for interior pointers |
| `Dv.while_` | `EWhile` |

The arities in that table are *not* the ML pipeline's: by the time a rule runs,
`Mono.erased_binders` has already deleted permissions, ghost sequences and the
`small_type` dictionaries (`small_type` is `U.raisable`, whose instance is
`non_informative`, so `must_erase_for_extraction` drops it).  `Reference.write`
takes two arguments here, not four.

This is also why `Rule_prim` receives the *type* arguments separately: they are
erased out of the value spine, but a buffer rule needs the element type to
build `TBuf t` (and `BufNull`).  `Extract.prim_app` collects them with
`Mono.type_binders`.

Four IR additions come with this: `TBuf` and `TRef` (§2.2), `EAny` for karamel's
`EAny`, and `EAbort of string` for `Pulse.Lib.Dv.unreachable` -- a `Dv`
function that Pulse emits where the proof says control never arrives.  It
prints as `failwith` in OCaml and as karamel's `EAbortS`.  In the karamel
backend a `TBuf` is a real C pointer, so a Pulse `let mut` scalarizes into a
plain local and a `Vec.alloc` becomes `KRML_HOST_MALLOC`.  `FStar.SizeT` is a
machine integer width (`Sizet`) like the `FStar.UInt*` ones, with the usual
conversion rules.

**`TRef` versus `TBuf`.**  A `ref` and a `box` point at one value; an `array`,
a `vec` and a `ptr` point at a run.  C and karamel make no distinction — both
are `t*`, and the same `BufRead`/`BufWrite`/`BufCreate` nodes serve for either,
which is why they share the operations rather than getting their own.  OCaml
does make the distinction, and it is worth making: a `TBuf t` is a `t array`,
but a `TRef t` is a `t ref`, so a `let mut` reads `!r` and `r := v` instead of
`(r).(0)` and `(r).(0) <- v` on a one-element array.

Each operation therefore chooses its OCaml spelling from the *type of its
pointer argument*, not from the node.  Two corners have no `ref` counterpart
and emit a `failwith`, the way `BufSub` on an array already does: a null
reference (`[||]` stands in for a null array, and there is nothing to stand in
for a null `ref`) and the `is_null` that tests one.  `Reference.to_array_mask`
and `Reference.array_at`, which view a reference as a one-element run, are
`BufSub` nodes for the same reason: in C they are the same pointer, in OCaml
they are not the same value.  `ArrayPtr.as_ref` and `from_ref` are still
identities, so a program that mixes those two libraries is C-only; the OCaml
backend will not silently mistranslate it, it will emit a file that does not
type-check.

A real Pulse program turned up four things that a small test does not:

- `Prims.Nil` and `Prims.Cons` have to be printed as OCaml's `[]` and `::`,
  in patterns as well as terms, because `FStar.Seq` is compiled to a list.
- `Layout.resolve` has to unfold type abbreviations (`TAbbrev`) before it can
  decide a layout; otherwise an `array` hidden behind an alias is not
  recognised and its elements are coerced through `Obj.magic`.
- `U.abs_formals` sees through nested lambdas, so a definition written
  `let f x = fun y -> e` has more binders than its type has arrows.  Each such
  extra binder consumes one arrow of the result type -- *and its effect*, which
  is the one that matters at the call site (§7).
- `U.abs_formals` also *opens* the binders under fresh names, while the
  computation type `specialize` returns still speaks of the ones it abstracted
  over.  The two have to be related by an explicit substitution: otherwise the
  result type mentions type variables that no binder introduces.  OCaml
  generalizes those away silently, but the karamel backend resolves a `TVar`
  positionally against `dl_typars` and fails outright.

`tests/custard/pulse/PulseHashTable.fst` is the standing regression for all of
this: it drives `Pulse.Lib.HashTable` (polymorphic, array-backed, linear
probing) from a `main`, and goes to *compiled and executed* OCaml as well as to
compiled C.  Note that `ht_t` stores its hash function in a field.  That is the
§3.2 `Poly` case as far as Custard's own monomorphization is concerned, and it
works: the field is a function pointer, the table is compiled once, and it is
karamel that specializes `ht_t` to `size_t`/`data` for C.

### 8.4 Garbage-collected references

Pulse's references are the ones with an explicit lifetime.  The other
reference API -- `FStar.All` in ulib, `FStarC.Effect` in the compiler, the
same three operations under two names -- has no `free` at all, because it is
realized by OCaml's own `ref`.  `Builtins.ref_rule` maps both:

| `FStar.All` / `FStarC.Effect` | IR |
| --- | --- |
| `ref` | `TRef t` |
| `alloc`, `mk_ref` | `BufCreate LHeap` of length 1, at `TRef t` |
| `op_Bang` (`!`), `read` | `BufRead` at index 0 |
| `op_Colon_Equals` (`:=`), `write` | `BufWrite` at index 0 |

`LHeap` rather than `LStack` because the cell outlives its scope -- nothing
here is a `let mut`, and there is no checker proving it does not escape.  For
the OCaml backend the distinction does not arise: a `TRef` prints as `t ref`
and a `BufCreate` into one as `ref x`, whatever the location says.  For the C
backend it does, and the honest statement is that these references are **not
supported there**: the allocation would be a `malloc` that nothing ever frees.
A C target must use Pulse's references, which have the lifetime the C backend
needs.  `tests/custard/Refs.fst` is the regression, on the OCaml side only.

This is what makes the compiler's own imperative style reachable: roughly
sixty `FStarC.*` modules allocate a `mk_ref` at the top level and mutate it
(§12.8).

### 8.5 Exceptions

`exception Bad of string & int` desugars to a data constructor of `Prims.exn`,
which is the one inductive with no `Sig_inductive_typ` behind it: `exn` is
extensible, any module may add a constructor, and there is no declaration to
hang fields on.  So `Extract.request` intercepts a constructor whose owner is
`PC.exn_lid` before the ordinary "request the type instead" path and emits a
declaration of its own, `DExn` -- which is what `MLM_Exn` is in the ML pipeline
(`Modul.fst:978`).  Erased binders are dropped exactly as they are for an
ordinary constructor, so building one agrees with declaring it.  `Prims.exn`
itself is a builtin rule mapping to `TExn`.

Nothing else about an exception value is special.  `Bad ("negative", n)` is an
ordinary `ECtor`, and `| Bad (s, k) ->` an ordinary `PCtor`, printed by the
same `ctor_ref` that a variant's constructors are -- which is exactly why the
declaration and the uses agree without a second mechanism.  Only the control
flow gets nodes:

| F\* | IR |
| --- | --- |
| `Prims.exn` | `TExn` |
| `exception C of t1 & t2` | `DExn` |
| `raise e` | `ERaise e` |
| `try_with (fun () -> e) h` | `ETry (e, [_cexn -> h _cexn])` |
| `failwith`, `exit` | externals; OCaml's own |

`ERaise` takes an *expression*, not a constructor and its arguments: the value
raised need not be built at the raise site, and making the node carry a
constructor would have meant special-casing something that `ECtor` already
does.  `ETry` gets a single catch-all branch because that is what the source
says -- F\* has no `try` syntax, so a handler is a function, and it does its
own matching on the value.  The thunk is unwrapped when it is syntactically a
lambda, the way `Pulse.Lib.Dv.while_`'s two halves are (§8.3).

Neither C backend has anything to say here: karamel drops a `DExn` with a
warning and compiles every use to `EAbortS`, and the direct backend rejects
both.  That is not a gap to be closed -- C has no exceptions -- it is the
statement that a program using them is an OCaml program.

One thing this does *not* do: a tuple field of an exception is not inlined the
way §5.7 inlines one in a constructor, so `exception Bad of string & int`
declares one field of tuple type rather than two.  `Simplify.inline_fields`
works from the constructor table a `DType` provides, and a `DExn` has no
`DType`.  `tests/custard/Exceptions.fst` is the regression.

---

## 9. Testing and validation

- **Golden tests**: `tests/custard/` with `.fst` inputs and `.expected` IR
  dumps (`--custard_dump_ir`), following the existing `mk/test.mk`
  `A.ml.expected` convention.  The examples in §3 are the first tests.
- **Differential testing against ML extraction**: for a corpus of pure,
  non-typeclass F* programs, extract with both pipelines to OCaml, run both,
  and diff the observable output.  This is the main safety net for the
  representation optimizations.
- **Execution tests**: extract to C via karamel, compile, run, compare against
  an OCaml-extracted oracle.
- **Krml round-trip**: check that Custard's `.krml` output is accepted by the
  in-tree `karamel/` submodule.
- **Performance tests**: the motivating case — a Pulse sorting algorithm
  parameterized by a comparison type class — should produce C with a direct
  call, no indirect call, and no dictionary struct.  Assert this on the
  generated C.
- **Regression corpus**: HACL*/Pulse entrypoints, tracked for extraction time
  and generated LOC.

---

## 10. Build integration

- New directory `src/custard/`, added to `src/fstar.include`.
- No changes needed to `mk/fstar-01.mk` / `mk/fstar-12.mk` beyond the include:
  the unified extraction pass extracts everything under `FStarC` already.
- The bootstrap implication: Custard is part of the compiler and so must
  itself be extractable by the *existing* ML extraction.  This means Custard's
  own source must avoid anything the ML extraction can't handle, and must not
  use type classes in ways that would be slow in the compiler.  (Amusing, but
  it does mean Custard cannot depend on Custard.)
- Stage0/stage1/stage2: adding a new `--codegen` value and a new attribute in
  `ulib/FStar.Attributes.fsti` requires the usual stage0 refresh dance.
  Sequencing: land the attribute and option first (inert), then the pipeline.

---

## 11. Decisions taken, and what is still open

### 11.1 Decided

1. **Partial application of `Mono` binders — reject** (§3.2a).  No automatic
   eta-expansion in v1: it cannot be done independently of the `Poly`-into-
   `Mono` problem, since eta-expansion creates exactly that situation.
2. **A `Poly` argument in a `Mono` position — reject in v1** (§3.2b), with
   *infer-and-promote* (retry with promotion) as the intended v2 answer.  This
   must be solved before eta-expansion is worth attempting.
3. **Function-valued `Mono` arguments — deferred to v2**, via ad-hoc
   defunctionalization (§3.8): a monomorphized function parameter expands to
   `(closure: Type) ([@@monomorphize] func: closure -> a -> b) (c: closure)`,
   and a call site's `(fun x -> foo x n)` expands to
   `UInt16.t closure_67 n`.  Independently, genuinely first-class closures must
   keep working (thread spawn, callbacks), so defunctionalization stays opt-in
   and `EFun` remains a real closure-forming node.
4. **Termination — fuel is enough** (§3.6), provided it fails *fast*: bounds
   are checked at `request` time, before the body is looked up or normalized.
5. **Effects need their own mechanism, not the §8 rule table** (§7).  Effect is
   a property of an arrow type, computed from the codomain;
   `[@@extract_as_impure_effect]` on `stt`/`stt_div`/`stt_atomic` means
   `a -> stt b p q` extracts like `a -> Dv b`, i.e. result-type projection plus
   promotion of the arrow to `E_Impure`, plus a drop/duplicate/reorder
   discipline on the resulting nodes.
6. **Polymorphic recursion — best effort** (§6).  Custard emits top-level type
   annotations, so OCaml should accept it; it is not a priority, and falling
   back to `TAny` is acceptable.
7. **Interfaces — Custard sees through them** (§4.2), as the ML extraction has
   since `--cmi` became the default.  When both `A.fsti.checked` and
   `A.fst.checked` exist, the loader must take `A.fst.checked`.
8. **Standalone programs only** (§4.4).  Libraries would have to define
   specialized entrypoints; this is the same constraint as Rust↔C FFI, where
   parametric types do not cross the language boundary.
9. **`--custard_monomorphize_types` defaults as proposed** (§2.1): on for
   direct-C, off for ML/Krml.  A worthwhile later relaxation: do not
   monomorphize a type parameter that is only used in erased positions.  Not a
   v1 priority.
10. **Debug info — mangled names are enough** (§2.3).  No `spec_key ↦ name`
    JSON map; the generated names are readable on their own.  (The mangling
    scheme therefore has to stay readable — prefer `bar__string` over a hash
    wherever it fits.)
11. **Type layouts are uniform in v1** (§5.0).  `foo int` and `foo prop` are
    compiled identically, because a function of type `foo 'a -> foo 'a` is
    compiled once and its projections must work at every instantiation.  Layout
    precision and type monomorphization are the same question; per-instantiation
    layouts fall out for free under `--custard_monomorphize_types`, and there is
    no middle setting.
12. **`Mono` is a property of a parameter, not a taint** (§3.2).  `Mono → Poly`
    is always fine, and anything projected or computed out of a `Mono` value is
    itself known at specialization time (`List.hd d` for a `Mono` `d` is a
    perfectly good `Mono` argument).  Only a genuinely runtime value reaching a
    `Mono` parameter is an error, and supporting *that* is a real performance
    cliff requiring manual opt-in — out of scope for v1.
13. **ANF runs first in phase 4** (§6), not last, because the purity discipline
    of §7.3 is much easier to enforce on ANF'd code.
14. **A fixed set of statement-shaped IR nodes** (§7.4) — `EWhile` plus
    reference/array `EOp`s — rather than an extensible block-carrying node.
    `Alloc`/`Free` stay separate impure operations; a scoped `EWithLocal` is at
    most an optional recovery, never a requirement.
15. **Mutual recursion across specializations** — emitting decls incrementally
    and computing SCCs once the worklist is drained (§6, pass 8) is the plan,
    and is what `Simplify.scc` does.  `tests/custard/Mutual.fst` covers a type
    cycle, a two-member function cycle and a three-member one.

### 11.2 Still open

1. **Canonical form of `Mono` arguments for interning** (§3.7).  Cannot be
   settled on paper: start with `Beta`/`Iota`/`Unascribe`, add `Primops` (almost
   certainly needed — `loop_unrolling` depends on `10-1` folding to `9`), and
   widen from there based on measurement.  The failure modes in both directions
   (duplicate specializations, wasted fuel) are cheap to observe, so this is a
   tuning exercise once M2 lands rather than an open design question.
2. **Scope recovery for stack allocations** (§7.4).  Pulse emits alloc and free
   as separate operations, so a scoped `EWithLocal` may simply not be
   recoverable in general.  The IR is designed not to need it; how far a
   best-effort recovery pass should go is open, and it is a C-quality question
   only.
3. **Manual opt-in for runtime-stored dictionaries** (§3.2).  Out of scope for
   v1, but if it is ever added, what does the opt-in look like — an attribute on
   the class, on the call site, or a separate "boxed dictionary" type?
4. **Layout precision between the two regimes** (§5.0).  v1 has only "uniform"
   and "everything monomorphized".  A middle setting (per-instantiation layouts
   for types that are never passed to a polymorphic function) is conceivable but
   needs a whole-program "is this type ever used polymorphically?" analysis; not
   obviously worth it.
5. **Which `option`/tuple representations to special-case** (§5.8), e.g. null
   pointers for `option t` in the C backend.
6. **CI coverage under demand-driven extraction** (§4.1) — accepted as expected
   behaviour, but the entrypoint set still has to be curated in practice.

---

## 12. Separate compilation

Everything above assumes one Custard run sees the whole program.  Two things
need that assumption relaxed.

- **Plugins.** An F\* plugin is loaded into a running compiler and calls into
  it.  Compiling a plugin has to mean "refer to the functions and types the
  compiler already contains", not "compile a second copy of the compiler".
- **Layered libraries.** EverParse wants a core `PulseParse`, then a CBOR
  library over it, then CDDL over that, and then one library per concrete CDDL
  format.  Each layer is built once and the next links against it.

A third thing wants *several output files* but not several runs, and is
covered separately in §12.9: hand-written OCaml realizations that reference
modules Custard compiles make the single output blob circular.  That is a
partition of one whole-program run, not a relaxation of it, and none of the
machinery below applies to it.

The framing that makes this tractable is that **a Custard unit is a whole
program with holes**, and that Custard already has exactly one place where a
hole could be filled: `Extract.request` (`Extract.fst:277`) is the single
choke point that turns "I need this definition" into "here is its name".
Separate compilation is teaching it a third answer, alongside "already
requested in this run" and "not yet requested": *someone else already built
that*.

### 12.1 What a unit is

Two options: `--custard_unit <name>` names the unit being built, and
`--custard_link <file.cui>` (repeatable) names units already built.

Roots are unchanged.  §4.4 still holds in full: Custard compiles what is
reachable from `--custard_entry`/`--custard_main`, a library still cannot
export a symbol with an unapplied `Mono` binder because there would be nothing
to name it after, and specialized entrypoints are still the idiom.  The single
addition is that a request may now be satisfied from an interface instead of
from source.

A declaration belongs to **whichever unit first emitted it**, and its
provenance is otherwise irrelevant.  In particular a unit that specializes a
combinator whose source lives upstream — the concrete-CDDL-format case, where
`cddl_parse@my_grammar` cannot possibly have existed when the CDDL library was
built — emits that specialization as an ordinary declaration of its own, lists
it in its own interface, and anything downstream reuses it.  There is no notion
of a private copy.

This is the same arrangement as C++ templates and Rust generics: generic code
crosses the boundary as *source*, instantiated code is emitted locally, and a
unit boundary is a **linking** boundary rather than an extraction boundary.

### 12.2 The unit interface

Alongside its `.ml` or `.c`, a unit emits a **unit interface**, `<unit>.cui`.
It lists *everything the unit emitted*, not only its roots: the object file has
symbols for all of it, so downstream should get to reuse all of it, and "which
of these was a root" is a fact about dead-code elimination that stops mattering
once the code exists.

Per declaration:

| field | why it has to be there |
| --- | --- |
| the canonical specialization key (§12.3) | this is what a downstream `request` looks up |
| the emitted symbol name | see §12.3: downstream must read this, not re-derive it |
| the post-`Layout`, post-`Rename` signature (binder `cty`s, result, `eff`) | so that a hit needs nothing else |
| for a type, its whole post-`Layout` `dtype` | erasure verdict, newtype collapse, dropped parameters, record versus variant, field names and order, inline fields |
| `Private`/`Rec` flags | `Rec` so that a downstream `scc` knows not to regroup |

Layout verdicts are recorded for **every type the unit reached**, including the
ones that were erased or collapsed to nothing.  A verdict is exactly the kind
of thing a downstream unit must not re-derive, and "this type has no runtime
representation at all" is as much a verdict as any other.

A header records the unit's name, the backend, every option that can change a
layout (`--custard_monomorphize_types` and friends), and the digests of the
checked files the run **loaded** — not merely of those that contributed an
emitted declaration.  The difference matters because of
`inline_for_extraction`: see §12.6.  Linking an interface built under different
options is an error rather than a silent mismatch.

The honest description of the format is that **a `.cui` is a serialized slice
of the post-`Layout`, post-`Rename` IR with the bodies stripped**.  It is not a
source-level interface, because none of the decisions it has to pin down are
source-level decisions.

Because that is what it is, it is written with the same
`Util.save_value_to_file` that stores a `.checked` file rather than with a
printer and parser of its own: the IR is plain first-order data, so the
mechanism already fits, and a hand-written text format would be several hundred
lines to keep in step with an IR still in flux for no benefit that the version
number in the header does not already give.  A `.cui` is a build artifact, not
something anyone edits; `--custard_dump_cui` covers the case where a human
wants to look.

One exception to "everything the unit emitted": the `Inline` declarations —
the projectors and discriminators that are substituted at their uses and never
emitted at all — are excluded, since exporting one would name a symbol that
does not exist.  A downstream unit re-derives them, which costs nothing.
Everything else is exported unconditionally, and §12.5 explains why that is
both possible and necessary.

### 12.3 The specialization key

Names do not need to be deterministic, and it would be a mistake to make the
design depend on their being so: two type-class instances for the same type
will always need a disambiguating subscript from somewhere.  The interface
records the **full emitted name**, and downstream reads it.  So
`spec_suffix`'s discovery-order counter (`Extract.spec_suffix`, `Extract.request`)
is fine as it stands, and making specialization names more readable — folding
the structural scheme `Monomorphize.request` already uses for types
(`Monomorphize.fst:134`, which is what produces `tuple3@tree_int_int_tree_int`)
over *all* the `Mono` arguments of a value specialization, instead of taking the
head symbol of the first — is output polish, decoupled from everything here.

What *does* have to be stable is the **key**, because that is the lookup.
Until M9a it was not, and the reason is worth recording because it was a live
bug independent of separate compilation:

```
string_of_key k = string_of_lid k.sk_lid ^ ... ^ show t
```

`show` on a `term` is `Print.term_to_string` (`Print.fst:166`), which
**resugars** unless `--ugly`, and the ugly printer prints an `fv` by its
**last identifier alone** (`Syntax.fst:629`).  The interning key was therefore
sensitive to a printing option, and under `--ugly` was not injective on names:
`A.inst` and `B.inst` both print as `inst`.

Measured, this bit.  `tests/custard/KeyNames.fst` — two `assume val tweak`s in
different modules, both passed to one `[@@@monomorphize]` binder — emitted a
single specialization under `--ugly` and printed `abab` where it should print
`abAB`.  What kept it rare is that `key_norm_steps` delta-unfolds a dictionary
to a record literal whose contents differ, so type classes never showed it;
what defeats that is an argument keeping an `fv` which does not unfold: an
`assume val`, a `[@@custard_extern]`, an abstract type constructor.

So keys have their own printer, `Extract.key_of_term` (§3.7): fully qualified
lids, α-canonical, universes erased, no resugaring, independent of every
printing option.  That is also exactly the string the interface stores.

### 12.4 What changes in the pipeline

1. **`Extract.request`** consults the linked interfaces before allocating a
   name.  A hit records a `DExternal` carrying the interface's signature and
   returns the interface's name, without normalizing or translating a body.
   This is where the saving is.
2. **A new `Imported of string` flag** on a declaration, naming the unit it
   came from, alongside `Private`/`Root`/`Erased`.  As implemented, imported
   declarations are kept *out of the program* rather than flagged inside it,
   which is a stronger version of the same thing: no pass can rewrite what it
   cannot see, and no pass had to learn about linking.  They are carried
   alongside — `Extract.imports` — and handed to the two places that do need
   them, `Layout.run` (for the verdicts) and the backend (for the namespace to
   qualify with).  The flag is still what marks them, so that those two places
   can tell.

   `Simplify.run` takes the imported declarations too, for `depat`, which
   needs a constructor's arity, and the `verdicts` table, so that a downstream
   use of an imported type is rewritten the way its home unit shaped the
   declaration rather than left alone.
3. **`Simplify.scc`** (`Simplify.fst:939`) treats an imported declaration as a
   leaf.  Units are acyclic by construction — a unit is whatever was reachable
   and not already in a linked interface — so a recursive group cannot span a
   boundary; the pass simply needs to know that it must not try.
4. **`Rename`** uses the recorded name verbatim for an imported declaration,
   and treats every imported name as taken so that a local definition cannot
   shadow one.
5. **`Driver`** writes the `.cui` after `Rename`, which is the only point at
   which both the layout verdicts and the final names exist.  `Layout.run` and
   `Rename.run` therefore both return the verdicts along with the program —
   `Rename` because it renames record fields, which a verdict names.

### 12.5 Why freezing the layouts is sound

> A type is either **imported**, and its layout is pinned by an interface, or
> **local**, and its layout is freely derived.  A value of one can never meet a
> value of the other.

Because a value crosses a unit boundary only through an imported signature, and
an imported signature mentions only types that are in the same interface.  A
downstream unit that reaches the same source type again and derives a different
layout for it is therefore harmless, provided interfaces are always consulted
first — which §12.4 rule 1 guarantees.

This is the load-bearing claim of the whole design, and it is the one to
re-examine first if something goes wrong.

The claim holds for a *layout* verdict because `Layout.run` takes the imported
verdicts as an argument and seeds its tables with them, marked pinned.  Seeding
rather than skipping is the point: uses of an imported type still have to be
rewritten — a constructor of a collapsed type collapses at a downstream call
site too — and the rewriter finds the rule in the same table it would have
found a locally derived one in.

The claim holds for a *representation* verdict — §5.5's record conversion and
§5.7's inline-field plan — for a different and better reason: those are no
longer whole-program decisions at all.  Both are computed in `Layout`, from the
declarations alone, so a downstream unit that asked would get the same answer.
They are still recorded in the interface (`ti_record`, `ti_plans`) and adopted
rather than re-derived, because an interface should say what it means and
because pinning keeps the claim true across a future change to the functions
that derive them; but nothing depends on the recording being there.

Getting to that point took three changes, and the reasoning behind each is
worth keeping.

- **`records`** used to refuse to convert a type that any surviving pattern
  still matched on — a fact about the program — because the IR had no record
  pattern to rewrite such a match to.  Adding `PRecord` removes the condition
  entirely, and the verdict becomes "one constructor, at least one field".
- **`inline_fields`**' plan was already declaration-local; its one
  whole-program ingredient was a scan for patterns that could not follow an
  expansion, and that scan turned out to be unreachable (§5.7).
- **`unused_params`** could not be fixed this way, only removed, which is what
  happened (§6).

What forced the issue was that the previous answer — a type whose shape the
passes changed is simply not exported, and a downstream unit compiles it for
itself — is not available.  Duplicating a *type* is harmless; duplicating the
declarations that mention it is not, because a global variable and an
exception both have nominal identity.  A downstream copy of a `let mutable`
would be a second cell, written by one unit and read by the other, and a
downstream copy of an exception would not be caught by the upstream `try` that
names it.  So every declaration has to be exportable, and therefore every
verdict a unit reaches about a type has to be one another unit would reach too.

That is the whole content of the principle in §5.5, and with it there is no
`stable_types` filter and no unpinnable case left to diagnose.

### 12.6 What separate compilation does not do

**It does not avoid loading the upstream sources.**  `inline_for_extraction`
and `unfold` are handled by `Eager_unfolding`/`Inlining` while the
*downstream* body is normalized (§4.3), which needs the upstream
implementation in the `TcEnv`.  So `Loader.ensure_loaded`
(`Loader.fst:60`) keeps working exactly as it does today, and the win is
skipping re-normalization, re-specialization and re-emission rather than
skipping I/O.

This is also why the interface's digest header covers every checked file the
run loaded.  A unit that inlines an upstream `inline_for_extraction` definition
depends on a body that appears in no interface at all; without that, editing
such a body would leave stale downstream units.

**It does not eliminate duplication.**  A specialization that did not exist
upstream is emitted by each unit that needs it.  Exporting them (§12.1) means
the duplication is between sibling units rather than between a unit and its
dependencies, and the answer when it matters is to put several formats in one
unit.  It is in any case an improvement on the status quo, which inlines
everything.

**It does not make rebuilds finer-grained.**  Custard emits one file per unit,
where the ML pipeline emits one `.ml` per `.fst` and rebuilds per module.  A
unit is a much coarser rebuild granularity; for a handful of units this is a
better trade than it sounds, but it is a real difference from how the compiler
is built today.

### 12.7 Names and clashes

Two units may independently emit a specialization of the same upstream
definition, and the mangled names will coincide.  OCaml resolves this for free
if each unit is a module; the direct-to-C backend needs a per-unit prefix on
every emitted symbol.  Neither requires the names themselves to be
deterministic (§12.3).

### 12.8 Compiling F\* itself: what else is missing

Separate compilation is a prerequisite for plugins but not the only gap between
Custard today and compiling the compiler.  What a survey of `src/custard/`
against `src/**/*.fst` turns up, in rough order of size:

1. ~~**Exceptions have no producer.**~~  Done: §8.5.
2. ~~**No rules for the garbage-collected references.**~~  Done: §8.4.  The
   remaining hole is that they are OCaml-only, which is the right trade for
   the compiler and wrong for anything targeting C.
3. ~~**The hand-written realizations.**~~  Done, as the per-module convention
   §8.2 asked for: `Rule_realized` and the list of realized modules in
   `Builtins`.  Nothing declared in one of the fifty-odd modules that `src/ml`
   or `ulib/ml` realizes is compiled — neither its types nor, since M10j, its
   values; each is referred to under the realization's own name.
   `FStar.Pervasives.Native`'s tuples and `option` are part of that, which is
   what makes the output callable from the realizations at all --- though
   those two are now printed as OCaml's own tuple and `option` rather than
   under the realization's name, which is the same type by the realization's
   own definition and needs nothing linked; see §8.2.

   Getting there was a bug hunt rather than a feature; each of these was found
   by advancing the OCaml build of the extracted compiler by one error.

   - An **abstract type lost its arity**.  `Sig_declare_typ` recorded
     `dt_params = []` whatever the kind said, so `FStarC.SMap.t 'value`
     declared a type constructor of no arguments.  Invisible while Custard
     compiled the declaration too — it was wrong on both sides — and an error
     the moment the declaration became the realization's.
   - An **eta-contracted type abbreviation dropped its arguments**.
     `type psmap = t` binds nothing and stands for a type *constructor*, so
     `psmap string` arrives at `Layout.resolve` with one more argument than
     the abbreviation has parameters; `List.zip` failed, the substitution was
     dropped, and so was the argument.  The surplus belongs to whatever the
     body resolves to.
   - `try_with`'s **thunk binder was dropped rather than bound**.  `fun () ->
     e` elaborates to a lambda whose body matches its binder against `()`, so
     the body does mention it; forcing the thunk by taking its body left that
     mention unbound.  It is now bound to `()`, which is what a call would
     have done, and the simplifier deletes the binding when it is unused.
   - `FStar.All.exit` was compiled to **OCaml's `exit`**, which takes an
     `int` where F\*'s takes a `Z.t`.  The realization is what narrows it, so
     the rule now names no target and lets each of `FStar.All`,
     `FStarC.Effect` and `FStar.Exn` resolve to its own support file.

   What the build stops on now is not this item: it is the 221 `Obj.t`s that
   `TAny` prints as, every one of them from `FStarC.Class.Monad` and
   `FStarC.Syntax.VisitM`.  `monad` is a class over `m : Type -> Type`, which
   is outside the IR's type language, so the dictionary's fields are `TAny`
   and OCaml has no coercions to make them typecheck.  That is item 6 below,
   not a realization problem.
4. **Plugins, native tactics and embeddings** have no counterpart at all.  This
   is not an independent item so much as the acceptance test for §12: a plugin
   *is* a separately compiled unit linking against the compiler.  Done (M10d),
   and it is `make custard-plugin`; see §12.12.
5. **§3.2b — a `Poly` argument in a `Mono` position — is a hard rejection**,
   and the compiler leans on `FStarC.Class.Show`/`Ord`/`Monad` everywhere.
   Measured (M9d).

   The first thing the measurement had to get right is *what to measure*.  A
   generic function is not a valid entry point — Custard compiles whole
   programs, and there is nothing to compile a generic `log_issue` *to* —
   so pointing `--custard_entry` at one and observing a §3.2b rejection says
   nothing at all.  The only honest root is a real program entry point.  With
   that settled:

   | Entry point | Result |
   | --- | --- |
   | `FStarC.Common.string_of_list` | Extracts |
   | `FStarC.Ident.string_of_lid` | Extracts |
   | `FStarC.Options.set_option` | Extracts |
   | `FStarC.Parser.ParseIt.parse` | Extracts |
   | `FStarC.Syntax.Print.term_to_string` | Extracts (~6 kloc of OCaml) |
   | `FStarC.Main.main` | §3.2b, at `FStarC.Class.Ord.sort_by` |

   `sort_by` is worth reading, because every rejection since has had its
   shape:

   ```fstar
   val sort    (#a:Type) {| ord a |} (xs : list a) : ML (list a)
   val sort_by (#a:Type) (f : a -> a -> ML order) (xs : list a) : ML (list a)

   let sort_by #a f xs =
     let d : ord a = { super = ...; cmp = f } in
     sort #a #d xs
   ```

   `sort_by` carries no class constraint, so nothing marks its `#a` `Mono`; it
   stays `Poly`, and the `sort #a` call is a §3.2b rejection.  It is `Mono` in
   everything but the annotation, and inferring exactly that is M7.

   Annotating `#a` by hand moves the rejection to `sort`'s *dictionary*
   binder, and this turned out to be a real gap rather than an inherent one.
   `d` is a local name; §3.2b saw a variable it did not recognize and stopped,
   even though `f` was by then known at specialization time.  Keys are now
   computed through local `let`s (see below), and with both `#a` and `f`
   annotated the whole thing specializes away — the emitted `cmp` for the
   `int` copy is literally `op_Subtraction`, and no `ord` record is ever built
   at run time.  `tests/custard/SortBy.fst` is this example.

   With `sort_by` annotated by hand, `FStarC.Main.main` advanced to
   `FStarC.TypeChecker.Primops.Sealed.ops`, whose first blocker was a *local*
   helper of the same shape — and that one needed no annotation at all, only
   §5.11's inlining, because a local function has no signature to annotate.

   Past it lies a blocker of a genuinely different kind, and the first one
   found so far that an annotation cannot fix.  `Sealed.ops` builds an
   embedding out of a value it just unembedded at runtime:

   ```fstar
   | [(ta, _); (tb, _); (s, _); (f, _)] -> … let emb = set_type ta e_any in …
   ```

   `ta` is a runtime argument, so the dictionary reaching `embed_simple`'s
   `Mono` binder is a runtime value, and no amount of annotation makes it
   known at specialization time.

   This was first read as the "stored in a runtime data structure" case,
   wanting an `[@@custard_extern]` realization or the opt-in dictionary
   passing that is out of scope for v1.  That reading was wrong, and looking
   at the term rather than the category is what corrected it: the dictionary
   is not a runtime value, it is a *static skeleton with one runtime leaf*.
   Every method in `e_sealed (set_type ta e_any)` is known; only `ta` is not.
   That is now §3.2c, which specializes on the skeleton and passes `ta` as an
   ordinary parameter, and `Sealed.ops` goes through.

   So the conclusion, with better evidence than the first attempt: the
   rejections are neither rare nor deep.  They are all one thing — a generic
   helper whose type parameter flows into a `Mono` position without being
   `Mono` itself.  For a *local* helper §5.11 now resolves it outright.  For a
   *top-level* one the diagnostic names the binder and the annotation always
   works, so what makes hand-annotation the wrong answer is only that there
   are many of them, spread across the library.  **M7's infer-and-promote is a
   prerequisite for compiling F\* itself.**  It is not a prerequisite for §12:
   the two are independent, and M10 can proceed on the code that already
   extracts.

   M7 is *not*, however, the whole remaining story, as an earlier draft of
   this section claimed on the strength of a single root.  Pushing past
   `sort_by` immediately produced the `Sealed.ops` case above, a second and
   quite different root that no inference can promote; §3.2c handles it.  The
   pattern across this whole exercise is worth stating plainly, because it has
   now repeated three times: each blocker looked like a deep limitation when
   named as a category, and turned out to be a specific and fixable shape when
   read as a term.

8. **Extraction ran away, and it was §5.11's fault, not the normalizer's.**
   With §5.11 in place `FStarC.TypeChecker.Normalize.normalize` consumed 73GB
   without finishing.  The plausible-looking explanation was that key
   normalization had diverged: `key_norm_steps` is deliberately the most
   aggressive reduction in the pipeline, it is *strong* (no `Weak`, no `HNF`,
   because a key has to be a normal form), and `Cfg.default_steps` sets
   `zeta = true`, so recursive definitions are unfolded unless `Exclude Zeta`
   is passed — leaving `Zeta` out of a step list does not turn it off, since a
   step list only ever adds.  Embeddings are exactly the kind of
   compositional, self-referential dictionary such a reduction would not stop
   on.

   That explanation was wrong, and adding `Exclude Zeta` changed nothing: the
   run still reached 73GB.  Tracing each normalization site showed the actual
   shape — the last *body* was normalized early and then nothing new was ever
   requested again, while argument normalization continued forever.  No new
   requests means no fuel spent, which is why §3.6's budget never fired; it
   also means nothing was diverging, since every key was a cache hit.  It was
   the same already-named code being re-extracted exponentially often, from
   §5.11 duplicating nested monomorphic helpers.  Restricting §5.11 to
   polymorphic local functions fixed it, and `Exclude Zeta` was reverted as
   unmotivated.

   Two things are worth keeping from this.  First, the diagnostic that
   actually discriminated was *whether fuel was being spent*: a runaway with
   no fuel spent cannot be a request loop, and cannot be a divergence either
   if the keys repeat.  Second, the hazard the wrong explanation described is
   real even though it was not this bug: `key_norm_steps` reduces with `zeta`
   on, so a definition reachable from a `Mono` argument can unfold without
   bound, and nothing in the term says so in advance.  **Every** normalization
   Custard performs therefore runs under `--custard_norm_budget`, through
   `Extract.norm_bounded` or `Mono.norm_bounded` --- the same wrapper, the
   first with the request chain of §3.6 attached and the second for the
   callers below the extractor.  Exceeding it is error 364, naming the term
   as written; `tests/custard/NormBudget.fst`.

   The two are not interchangeable and the split is not cosmetic: a budget is
   only useful if the message says *which* definition was being reduced, and
   below the extractor there is no chain to say it with.  Anything that
   normalizes and does have a chain should use `Extract.norm_bounded`.

6. ~~**Higher-kinded classes have no representation.**~~  **Done.**
   `FStarC.Class.Monad` is a class over `m : Type -> Type`, and the IR's type
   language has no such binder, so `monad`'s `return` and `bind` fields are
   `TAny` and the OCaml backend prints them as `Obj.t`.  221 of them survive
   into the extracted compiler, all from `Class.Monad` and `Syntax.VisitM`.
   `m t` is genuinely not an OCaml type, so the coercions are not avoidable and
   the answer is to insert them *exactly* at the `Obj.t` boundary and nowhere
   else: `Simplify.coerce_prog`, described in §5.4.  573 coercions in the
   extracted compiler, one in the whole `tests/custard` corpus outside the two
   modules written to exercise this.  Specializing the dictionary away — the
   hole abstraction of §3.7, extended to reach a type-constructor argument —
   remains the better answer where it applies, and would reduce the `TAny`
   count rather than coerce around it; marking `Class.Monad`'s and `VisitM`'s
   arguments `[@@@monomorphize]` is the cheap version of the same thing.  Both
   are cleanup, not blockers.

   Two further bugs surfaced behind this one, both about realized modules
   (§8.2):

   - A realized type abbreviation was being expanded.  `FStar.Dyn.dyn` is
     `unit -> Dv value_type_bundle` in the F\* source and `Obj.t` in
     `FStar_Dyn.ml`; expanding it replaced a type the target has with one it
     does not.  `Layout.resolve` now stops at a `Realized` declaration.
   - …but `FStarC.PSMap.psmap` is `inline_for_extraction type psmap = t`,
     written that way precisely "so we don't have to define these in the
     underlying ML file".  So the discriminator is the qualifier: `Extract`
     marks a realized type `Realized` only when it is *not*
     `inline_for_extraction`.

   What the extracted compiler's OCaml build stops on now is neither: a
   realized module's signature mentioning a type Custard compiles.
   `FStarC.Parser.ParseIt`'s `ASTFragment` carries a `FStarC.Parser.AST.file`,
   and `FStarC_Parser_AST.modul` (from the ML-extracted `fstar.compiler`) is
   not `fStarC_Parser_AST_modul` (from Custard).  This is item 3's transitive
   closure argument reaching a module with no hand-written `.ml` at all.  It
   is *not* §12: nothing here wants a second extraction run.  It is §12.9,
   output splitting — **done**, and §12.10 records where the build reached
   with it.
7. **Build integration.**  One file per unit against the current per-module
   `.ml`; see §12.6.  `--lax` is not a concern: it only admits SMT queries, and
   leaves syntax, elaboration and the checked files unchanged.  **Done** for
   the compiler itself: `make custard`, described in §12.11.
8. Smaller: `Prims.int` maps to a fixed-width integer on the Krml path
   (`PrintKrml.fst:111`), which is fine for an OCaml target and a latent
   miscompilation for a C one; and `FStar.Printf`'s type-level arity
   computation has no story, though the compiler itself sidesteps it by using
   `FStarC.Format`'s hand-unrolled `fmt1`..`fmt6`.

---

### 12.9 Output splitting

Separate compilation is not the only reason the output cannot be one file, and
the other reason is not about relaxing the whole-program assumption at all.

**The problem.** F\* has fifty-odd hand-written OCaml realizations (§8.2), and
fourteen of them reference modules Custard compiles:

| realization | references |
| --- | --- |
| `FStarC_BaseTypes` | `FStar_Int8/16/32/64`, `FStar_UInt16` |
| `FStarC_Extraction_ML_PrintML` | `FStarC_Const`, `FStarC_Options`, `FStarC_Parser_Const_Tuples` |
| `FStarC_Filepath` | `FStarC_Platform` |
| `FStarC_Parser_LexFStar` | `FStarC_Errors`, `FStarC_Ident` |
| `FStarC_Parser_ParseIt` | `FStarC_Parser_AST`, `FStarC_Errors`, `FStarC_Options`, … |
| `FStarC_Reflection_Types` | `FStarC_Syntax_Syntax`, `FStarC_TypeChecker_Env`, … |
| `FStarC_Syntax_TermHashTable` | `FStarC_Syntax_Hash` |
| `FStarC_Tactics_Native` | `FStarC_Tactics_Monad`, `FStarC_TypeChecker_Cfg`, … |
| `FStarC_Tactics_V2_Builtins` | `FStarC_Syntax_Syntax` |
| `FStarC_Unionfind`, `FStar_IO`, `FStar_Issue`, `FStarC_Util`, `FStar_Reflection_Typing_Builtins` | shallower |

So the reference graph alternates: Custard output → realization → Custard
output → …, and one blob gives OCaml a cycle.  OCaml compilation units must
form a DAG.  `module rec` is single-file only, requires an explicit signature
on every member, and is limited by the initialization-safety check, so it is
not an escape.

**There is no real cycle.**  F\*'s module graph is a DAG and every realization
sits at a node of it — which is exactly why `fstar.compiler` builds today with
the same realizations.  The cycle is created by emitting one file, and it is
removed by emitting several.  This needs no second extraction run, no unit
interface, no re-specialization and no version negotiation; it is one
whole-program run whose already-topologically-sorted declaration list is cut
into pieces.  That is a *different mechanism* from §12.1–12.8, and conflating
the two is what made item 6 above look like a §12 problem.

**Where to cut.**  One file per F\* source module, which is what ML extraction
already does and what the existing build expects.  `ocamldep` over the
generated `.ml` files together with the hand-written ones then computes the
link order, correctly and with no table to maintain — including the parts of
each realization's dependencies that its `.fsti` does not mention
(`FStarC_Parser_ParseIt.ml` calls `FStarC_Parser_Parse`, which is nowhere in
F\*'s dependency graph).

**The one wrinkle: monomorphization detaches a declaration from its module.**
`fStar_List_map__term` is born in `FStar.List` but mentions
`FStarC.Syntax.Syntax`, and `FStarC_Syntax_Syntax.ml` references `FStar_List`
— a cycle, from a specialization rather than from a realization.

A valid slot always exists.  A specialization is created *because* some module
`U` instantiated it, so `U` depends, in F\*'s graph, on every module the
specialization mentions; any linear extension of the DAG therefore has room
after all of them and before `U`.  The rule that finds it:

> `home(d)` is the latest, in the *module order*, of `d`'s own module and the
> homes of everything `d` references.

One forward pass over the sorted program computes this, because every
reference is already earlier in the list.  A declaration whose home is its own
module is *at home*; everything else has been **relocated**.

**The module order is the generated program's, not F\*'s.**  F\*'s dependency
graph is the obvious candidate and it is the wrong one, because it is a graph
over *sources* and the question is about *targets*.  It records a dependency on
an interface where the code that comes out refers to the implementation's
contents; it does not know that `FStar.Stubs.X` and `FStarC.X` have become one
module (§8.2); and it has no opinion at all about the modules Custard
synthesises.  So `Split.module_ranks` builds a graph whose nodes are the target
modules and whose edges are the references actually emitted, and ranks by a
topological sort of it.  That makes the invariant the split relies on --- every
reference points at an earlier file --- true by construction, and a declaration
then has to leave its own module only when it is caught in a *real* cycle
between modules.

Two details make that well-defined.  The reference graph can have cycles, so it
is condensed with Tarjan (`Split.sccs`): components come out in dependency
order, and inside a component --- where the modules genuinely do refer to each
other, and no order is right --- the members are ordered by F\*'s source order,
which is the order under which the fewest declarations have to move.  And the
reference graph leaves the order of two mutually unreferencing modules free,
which still matters, because the output is one flat directory in which a
hand-written realization may sit anywhere; F\*'s source order is the tie-break
throughout, and the fallback rank for a module that emits nothing at all.

A realization is a fixed point of all this: it is a file Custard does not
write, so it cannot be relocated and its rank is simply its source rank.  The
declarations around it move instead, which is the whole point.

**Names.**  A realization refers to `FStarC_Parser_AST.decl`, not to
`FStarC_Parser_AST.fStarC_Parser_AST_decl`, so the split output has to present
the ML-extraction API — which it can, because mangling only ever existed to
keep one flat file collision-free (§12.7).  A declaration that is at home and
is the only declaration from its source lid is emitted under its plain
identifier, with its constructors under their plain identifiers; a relocated
declaration, and every specialization, keeps its mangled name.  Cross-file
references are qualified by module.

This reuses the `Imported` flag wholesale: when file *i* is printed, every
declaration from an earlier file is marked `Imported`, which already means
"not printed here, referred to as `Module.name`" (§12.2), and every
declaration from a later file is dropped.  So the splitter is a partition plus
a loop, and no printing path learns about it.

**A realization's callees have to be roots.**  Dead-code elimination cannot
see a call from hand-written OCaml, so a definition that only the realization
uses is dropped.  `--custard_entry` names it, which is the same idiom §4.4
already asks of a library.  `tests/custard/SplitLo.add_one` is the regression.

**A realized module can still contribute a file.**  A realization replaces its
module's values as well as its types (§8.2), so most of what a realized module
would have contributed is now an external and takes no space at all.  What is
left is what §8.2 exempts — a projector, an `inline_for_extraction` alias such
as `FStarC.PSMap.psmap`, `FStar.Pervasives.Native.fst` — together with any
specialization that lands there by the relocation rule.  None of that can go in
the file the realization occupies, so it goes in `Custard_<Module>.ml`, under
mangled names since nothing in it is at home.  Five such files survive in the
compiler today.

**What splitting does not do.**  It does not make Custard's data layout agree
with ML extraction's.  A realization that only *names* a Custard type — which
is what nearly all fourteen do — is fine, but one that constructs or matches a
Custard value depends on Custard's §5.5 and §6 verdicts for that type matching
what the hand-written code assumes.  `FStarC_Errors.Error` is the one case in
the compiler that does this today.  Where they disagree the answer is the same
as for any other realization mismatch: state the layout in `Builtins`, or
realize the type too.

### 12.10 Where the extracted compiler stands

With splitting, `--custard_entry FStarC.Main.main --custard_split` produces
**185 files**, and those together with the hand-written realizations of
`src/ml` compile, in `ocamldep -sort` order, link, and run.  Getting the *build*
that far is what the rest of this section records; "It runs" below is what came
after.

Getting there was a matter of advancing the build one error at a time.  Two
kinds of thing came up, and it is worth keeping them apart.

**Custard bugs.**  Five, each a real one that a smaller test had not reached:

- **A type argument in value position.**  `Mono.keep_thunk` puts the last
  binder back when dropping it would turn a definition into a value, and the
  binder it puts back may be a *type* binder — as it is for an unannotated
  polymorphic value like `let trie_empty = { bindings = []; namespaces = [] }`.
  The definition then took a runtime argument that the call site answered with
  the type, which happened to work where the type was concrete (§5.4 wrapped it
  as `Obj.magic ()`) and emitted an unbound identifier where it was a type
  variable.  A retained type binder carries no value, exactly like a
  unit-shaped one, so `Mono.unit_binders` now includes it and the call site
  passes `()`.  The binder is typed `unit` rather than by its sort, which is
  both honest and the only typing that needs no coercion.
- **A lambda-lifted local function that did not receive its callees'
  captures.**  A reference to a lifted local becomes a call to its top-level
  name applied to *its* captures (§5.10), so a nest that mentions another
  lifted local does not capture it — it captures what that one captures.
  `Extract.lift_letrec` was taking `Free.names` at face value and emitting
  bodies that named variables no parameter bound.  It now expands a free
  variable that is itself lifted into that nest's captures.
- **A lambda-lifted local function that kept its own type binders as
  parameters.**  F\* generalizes a local `let rec` just as it does a top-level
  one, so `let rec collect (l : list 'a) = ...` binds `'a`.  Those binders hold
  no runtime value and no call site passes them (§5.0); they belong in the
  declaration's `dl_typars`, not its binders.  Left as binders they made every
  call arity-mismatched.
- **An eta-contracted abbreviation unfolded with its own parameter free.**
  `uvars = FlatSet.t ctx_uvar` goes through `t = flat_set`, which binds
  nothing, to `flat_set a = list a`, which binds one thing.  Both
  `Layout.resolve` and `Monomorphize.unfold_cty` resolved the body first and
  applied the surplus argument to the *result*, yielding `(t, ctx_uvar) list`.
  The surplus has to be attached before the body is resolved.
- **An arrow hidden behind an abbreviation.**  `let st a = ctxt -> ML (a &
  ctxt)` makes `let get : st ctxt = fun s -> (s, s)` a definition with one
  binder whose declared type is an application, not an arrow, so the result
  type was emitted whole and the binder emitted as well.  The result type is
  now unfolded to weak head normal form before the extra binders' arrows are
  peeled off.

**Realizations written against the ML extraction.**  These are not Custard
bugs; they are places where a hand-written `.ml` assumed something the ML
extraction did and Custard does not.

- **Type abbreviations.**  Custard unfolds them rather than emitting them — a
  monomorphized abbreviation has no generic form left to emit, and the backends
  need the representation behind the name (§5.0) — so an abbreviation that only
  a realization mentions is reached by nothing and dropped as dead.
  `--custard_entry` names it, exactly as §12.9 uses it for a realization's
  callees, and a root is a root whichever kind of declaration it is.  It took a
  fix in two places: `Extract.run` only flagged a `DLet` as a `Root`, so §6
  pass 6 dropped a type root as dead; and `Driver.check_entrypoints` looked
  the entry up in an environment that had not loaded its module yet, which is
  stricter than the extraction loop, which loads on demand (§4.2).  The check
  now covers what is loaded and `Extract.run` reports a root that produced no
  declaration.  `tests/custard/TypeEntry.fst` pins this.
- **Constructor arity.**  F\* declares `MLP_CTor of mlpath & list mlpattern`
  with *two* arguments and Custard emits it that way; the ML extraction packs
  them into a tuple.  Writing the pattern out — `MLP_CTor (path, ps)` rather
  than `MLP_CTor args` — means the same thing under both, which is what
  `FStarC_Extraction_ML_PrintML.ml` now does.
- **Private symbols.**  `FStarC.Parser.Const.Tuples.is_tuple_constructor_string`
  was used by a realization without being in the interface, so no entry point
  could name it.  It is exported now.

What the build stops on is one more of the second kind.
`FStarC_Parser_Parse.mly`, the hand-written grammar, spells out
`FStarC.Parser.AST`'s constructors, and §5.5 collapses a one-constructor type
into its payload: `CalcStep of term & term & term` is a constructor with *one*
argument of tuple type, so `calc_step` is that tuple and `CalcStep` is not a
name in the emitted code at all.

The rule that settles this is §5.5's, not a new one.  A representation is a
property of a type, decided by the type and what it contains, and never by
which of its users happen to be outside the extracted program — the same
principle that removed unused-parameter elimination in M10f and moved the
inlining and record passes into `Layout` in M10g.  A root type is emitted, and
that is all being a root means.  So the realization gives: the AST already
carries `mkTuple`, `mkDTuple`, `consTerm` and friends for exactly this reason,
and a constructor a realization needs is reached through a function in the F\*
source, which is compiled code and therefore right under either extraction.

#### It runs

With those out of the way the split compiles, links and **runs**: a
Custard-extracted `fstar.exe` verifies `FStar.List.Tot.Properties` from source
in about nine seconds and reports the same errors on the same programs as the
one dune builds.  Six further code-generation bugs stood between "compiles" and
"runs", and they are worth recording because each was invisible to the test
suite:

- **A `ref` dereference printed as an array read.**  ANF introduced
  `let tmp = e ...` whose type came out `TAny`, so the backend's `TRef?` test
  failed and `!x` printed as `x.(0)`.  Two causes, both fixed: under `--lax` a
  typechecker-invented binder has no sort, so the local `let`'s own right-hand
  side is now recorded and consulted (`Extract.lettys`); and a type
  *abbreviation* is a name, not a shape, so applying arguments to a value of
  abbreviated function type, or reading its effect, has to unfold it first
  (`Extract.abbrevs`/`unfold_abbrev`).
- **A negative literal erased to `()`.**  `-1` reaches the extractor as
  `Tm_lazy`, because the normalizer hands a reduced arithmetic result back as
  an *embedding*, and `expr_of_term`'s catch-all silently erased it.
  `U.unlazy_emb` at the top of `expr_of_term`.  `tests/custard/Literals.fst`.
- **Extraction that depended on request order.**  `TcEnv.try_lookup_lid`
  returns `None` when the lid's module has not been loaded yet, and every
  caller's fallback --- do not erase, do not filter, assume impure --- is
  *silently wrong* rather than conservative.  Since loading is on demand
  (§4.1), the same definition came out differently depending on what had been
  extracted before it: a type constructor whose kind could not be read kept its
  dictionary argument as if it were a type argument.  All nine sites now go
  through `Extract.lookup_lid_typ`, which loads first.
- **An under-abstracted type abbreviation.**  `let mymon = writer (list ps)`
  has kind `Type -> Type` and binds nothing; the IR has no partial application
  of a type constructor, so `extract_type_abbrev` eta-expands it from the
  binders of its own type.  `tests/custard/Mymon.fst`.
- **Two lambda-lifted binders collapsed into one.**  `U.abs_formals` invents
  *fresh* names for the binders it opens, and `lift_letrec` called it twice ---
  once for the binders, once for the body --- so the body named variables no
  binder bound.  Where the two binders were both the compiler-generated
  `uu___` of an inlined pattern, the emitted `match (tmp, tmp1)` came out as
  `match (tmp, tmp)` and the second argument was silently dropped.  Opened once
  now.  `tests/custard/Patlift.fst`.
- **Ambiguous record expressions**, §5.5.

Two things are known not to work yet.  A Custard-built compiler cannot read
`.checked` files written by a dune-built one, and vice versa: a checked file is
a `Marshal` dump, and the two extractions lay the same F\* types out
differently.  That is expected and not a bug --- the cache is already versioned
--- but it does mean a Custard-built compiler has to build its own cache.  The
second, the ulib **plugins**, is gone: they are compiled by Custard into the
same program now (M10p, §13), so `mk_class` and the rest register into the
tables the compiler actually reads.

Build integration --- item 7 of §12.8, which has to drive `menhir` and `sedlex`
for the generated parser and lexer and link the result --- is §12.11.  Beyond
that the `Prims.int` question of item 8 remains.

---

### 12.11 `make custard`

The recipe of §12.10 lived in shell one-liners for as long as the question was
whether it could work at all.  It is now `mk/custard.mk`, reached by `make
custard` (and `make custard-smoke`), building into `stagec/`.  It depends on a
stage 2 compiler, which it needs twice over: to *run* the extraction, and for
the `.checked` files the extraction reads.

The entry points are no longer a command line.  `src/custard/entrypoints.txt`
lists them one per line, `#` for comments, and the makefile turns each line
into a `--custard_entry`.  Two kinds of line appear there, and the file says
which is which: a declaration that some hand-written realization calls, which
nothing in F\* refers to and demand-driven extraction would otherwise drop
(§12.9); and a bare *module* name, kept for its initializers (§4.4).

The four steps:

1. **Cache.**  `stage2/ulib.checked` and `stage2/fstarc.checked` merged into
   one directory, because `--cache_dir` takes one.  It is a copy, so it has to
   depend on the checked files themselves and not just on the makefile: a
   stale cache is not a build error but a *silent* one, in which the previous
   interface of an edited module is what extraction reads.  What it looks like
   is a link failure in generated code — the last one was `Unbound value
   FStarC_TypeChecker_Primops_Base.mk1`, from Custard finding only the old
   `Sig_declare_typ` and emitting a `DExternal`.  Which gives the general
   diagnostic: a reference printed as `Module.lowercase_id`, with a dot, in
   unsplit output is an external or a realization; an ordinary reference is a
   single mangled identifier, `fStarC_..._id`.
2. **Split.**  `--codegen Custard --custard_split` from `FStarC.Main.main` plus
   the entry file, into `stagec/split/` --- 185 files.
3. **Assemble.**  Those, plus `src/ml/*.ml`, plus a two-line `zzMain.ml`, into
   one flat directory.  The realizations win where a file exists on both sides:
   a realized module's F\* definitions are a model and Custard does not emit
   them (§8.2).  `FStarC_Version.ml` is generated here rather than copied from
   the dune build, because it assigns to `FStarC.Options`' `_version`, and
   Custard mangles a leading underscore to `u__` (§5.2) where the ML extraction
   does not.
4. **Parsers, then compile.**

The parsers are the only interesting part.  `menhir --infer` types a grammar's
semantic values by compiling a mock module against the surrounding code, and
the surrounding code here is *Custard's* `FStarC_Parser_AST`, not the ML
extraction's.  Borrowing the dune build's answer would be relying on the two
extractions happening to lay out `FStarC.Parser.AST.term` the same way.  So the
makefile drives menhir itself:

```
menhir --infer-write-query M.mock.ml M.mly
ocamlfind ocamlc -I . -i M.mock.ml > M.reply
menhir --explain --infer-read-reply M.reply M.mly
```

This needs `.cmi`s for everything the grammar's header opens, which is a
chicken-and-egg: those modules are upstream of the parser, but `ocamldep` sees
the whole set at once.  The way out is that they really are upstream, so a
best-effort pass that runs `ocamlfind ocamlc -c` over `ocamldep -sort` order
and *ignores every failure* is guaranteed to compile them; the modules that
fail are exactly the ones downstream of the parser, and the final `ocamlopt`
pass compiles everything again in order anyway.  Bytecode, because only the
`.cmi` is wanted and `ocamlc` is much the faster.  `sedlex` needs no such
help --- `-package sedlex.ppx` applies the ppx to the two lexers directly.

The note in earlier drafts that editing `FStarC_Parser_Parse.mly` requires a
full `make` is therefore obsolete.

`make custard-smoke` checks `FStar.List.Tot.Properties` from source with the
result, in a fresh `--cache_dir`: as §12.10 says, a Custard-built compiler
cannot read a dune-built one's `.checked` files.

### 12.12 `make custard-plugin`

Item 4 of §12.8 --- a plugin compiled by Custard, linking against a compiler
compiled by Custard --- is the acceptance test for this whole section, because
a plugin is the one thing that is *both* a separate compilation unit and a
consumer of the compiler's own types.  It is `make custard-plugin`, and it is
about forty lines of `mk/custard.mk`:

1. check `tests/custard/plugin/CustardPlugin.fst` into the same `--cache_dir`
   the compiler's own extraction used;
2. extract it with `--custard_unit CustardPlugin --custard_link
   stagec/split/fstarc.cui`, which is a *second* whole-program run that
   happens to have the compiler as its upstream unit;
3. `ocamlopt -shared -I stagec/build`;
4. run `stagec/out/bin/fstar.exe --load_cmxs` on
   `CustardPluginTest.fst`.

The extraction in step 2 runs with the *dune-built* compiler, because the
`.checked` files are its; the load in step 4 runs with the Custard-built one.
Anything else would test nothing.

The test file reduces four applications with `norm [primops]` and `trefl`,
and every definition it applies is `irreducible`.  That is the whole point:
with the plugin loaded they reduce, and without it the tactic fails with
error 228, so the test cannot pass by having the interpreter quietly unfold
the definitions instead.  An earlier version without `irreducible` passed
with the plugin *and* without it.

#### Linking against a split unit

A `.cui` written before M10d recorded only the *unit* name, which is all a
reference needs when the upstream was emitted as one file: the reference is
`Unitname.x`.  But the compiler is built with `--custard_split`, so its
declarations live in one file per F\* module and most of them are emitted
under their plain identifier, at home in their own file.  A downstream unit
that says `Fstarc.fStarC_Ident_lid_of_str` finds nothing.

The observation that makes this small is that **an import from a split
producer is the same thing as a cross-file reference inside a split output.**
Both are "this name lives in that file"; the only difference is which run
emitted it.  So the `.cui` entry gains an `ue_home : option string`, the F\*
module whose file the declaration was written to, and `PrintOCaml.build_tables`
folds every import that carries a home into the same `homes` table a local
split fills in.  Nothing else in the printer changes --- including the
at-home test, which reproduces the upstream's naming decision exactly because
the `.cui` carries the *post-`Rename`* name.  The `.cui` format version goes
7 → 8.

`Driver.run` therefore has to split *before* it writes the unit interface,
which is the reverse of the old order; the split's result is kept so that
`write_unit_iface` can consult it.

#### The loader has to register dependences

Desugaring a declaration resolves the names it mentions, so before
`FStarC.TypeChecker.NBETerm`'s `val`s can be desugared, `FStarC.Effect` has
to be in the desugaring environment --- `ML` is one of its names.  Batch mode
gets that for free by walking the dependency graph in order, and so does a
whole-program run rooted at `FStarC.Main.main`, which transitively reaches
everything.  A *plugin* run does not: its compiler-side references arrive
through a linked unit, not through its own imports, so `Loader.ensure_loaded`
pulls a module in on demand with nothing underneath it.

`ensure_loaded` is now recursive: before registering a module it
`ensure_loaded`s each of that module's own dependences.  A `loading` set
breaks the cycle, which is real --- a module's dependences include its own
interface.


## 13. Plugins

A definition marked `[@@plugin]` is compiled like any other definition, and in
addition gets a *registration*: a top-level effectful `let` that installs it in
the normalizer, together with the embeddings that convert between F\* terms and
the compiled function's own arguments and result.  This is what makes
`FStar.Tactics.Typeclasses.mk_class` run as compiled OCaml instead of being
interpreted, and until it exists a Custard-built compiler cannot check anything
that resolves a typeclass instance.

`FStarC.Custard.RegEmb` is the Custard counterpart of
`FStarC.Extraction.ML.RegEmb`.  The generated code is the same code.  It is
generated differently, and that difference is the whole design.

### 13.1 Generate F\* syntax, not IR

The ML pipeline builds the interpretation function directly in ML syntax:
`MLE_App`, `MLE_Fun`, `MLTY_Top` everywhere, names spelled as `mlpath`s.  It
has to, because by the time it runs there is no F\* term left to speak about.

Custard does not have that constraint, and generating IR would be a second,
untyped copy of the extraction loop: every embedding it names is a definition
that has to be *requested*, an `embedding a` is a typeclass-shaped value that
has to be specialized (§3.1), the tactic combinators it calls are `Tac`
functions that have to be reified (§7.5), and their arguments are subject to
erasure (§5).  Doing any of that by hand means getting all of it right by hand.

So `RegEmb` builds the interpretation function as **F\* syntax** and hands it to
`Extract.expr_of_term`.  Requesting, specialization, monomorphization, erasure
and reification then happen exactly as they do for hand-written code, and the
result is typed IR rather than a pile of `TAny`.

The one thing that cannot be generated this way is the outermost call:
`FStarC.Tactics.Native.register_plugin` and `register_tactic` are defined in
`src/ml/FStarC_Tactics_Native.ml` and are deliberately *not* in the module's
`.fsti`, so there is no lid to refer to.  Those two are synthesized as
`DExternal`s and applied in raw IR --- one node each, and nothing below it.

### 13.2 What is generated

For `f : t1 -> ... -> tn -> Tac r` the registration is

```
let __plugin_f : unit =
  FStarC_Tactics_Native.register_tactic "M.f" (n+1)
    (fun psc ncb us args ->
       mk_tactic_interpretation_n "M.f (plugin)" f e1 .. en er psc ncb us args)
```

and for a pure `f : t1 -> ... -> tn -> r`

```
let __plugin_f : unit =
  FStarC_Tactics_Native.register_plugin "M.f" n
    (fun psc ncb us args ->
       arrow_as_prim_step_n e1 .. en er f (lid_of_str "M.f") ncb us args)
    (fun ncb us args -> NBETerm.arrow_as_prim_step_n ... )
```

Three things are worth spelling out.

**Binder sorts come from the callee.**  The generated lambda never invents a
type for its own binders.  `signature_of` looks the callee up, instantiates its
leading implicit binders with the type arguments being passed, and returns the
remaining binders; the lambda is built over *those*.  Every function the
generated code calls happens to be polymorphic only in leading implicits ---
which is what F\* makes of a `'a` --- so inserting the type arguments
positionally is right, and `signature_of` raises if a binder it was told is
implicit is not.  The single exception is the `psc` binder of the pure case,
which the syntax-kind interpretation ignores and no callee mentions; its sort
is spelled `FStarC.TypeChecker.Primops.Base.psc` by hand.

**Reification makes `from_tactic_n` unnecessary.**  The ML pipeline wraps the
plugin in a chain of `from_tactic_n` identities to move between ulib's `Tac`
and the compiler's `tac`.  In Custard the two *are* the same type: §7.5
compiles `Tac a` to `ref_proofstate -> Dv a`, which is what the compiler's
`tac a` is, so the compiled plugin already has the type
`mk_tactic_interpretation_n` expects and the wrappers are dropped.

**No NBE interpretation for tactics.**  ML computes one and `register_tactic`
discards it.  Custard does not compute it.

### 13.3 Which modules get registrations

Registrations are generated only for a module named by `--custard_entry`.

Custard loads a module because something in it is called, which says nothing
about whether its plugins are wanted: a program that merely uses `FStar.Tactics`
would otherwise acquire a registration for every `[@@plugin]` in the tactic
library, and with it all the embedding code they reach.  Naming the module is
the request --- and it is the same thing that makes the plugin's own definition
a root, since a plugin is a leaf of the program and nothing calls it.

Two consequences for the loader, both of which needed fixing:

* A module named this way need not be reachable from the file on the command
  line, so it is absent from the *dependency graph* even though it is in the
  file system map.  `Parser.Dep.deps_of` reported such a file as having no
  dependences at all, which is indistinguishable from the truth about `Prims`
  and made its checked file fail validation (§4.2's digest check).  It now
  falls back to parsing the file, exactly as `--ext fly_deps` does for the
  command-line file.
* The `per_module` callback fires inside `Extract.run`'s *initializer fixpoint*
  (§4.4).  It has to: generating a registration is itself a source of requests,
  and hence of newly loaded modules --- `FStarC.Tactics.InterpFuns` is not
  otherwise mentioned by the compiler --- whose own initializers must then run
  as well.

### 13.4 Embeddings

`embedding_for` maps a type to a term of type `embedding t`.  A table copied
from the ML pipeline covers the ground types and the parameterized ones
(`list`, `option`, tuples, `either`, `sealed`); a `[@@plugin]` *datatype* is
supposed to come with a generated `e_<name>` beside it.  Reaching either
requires weak-head-normalizing the type first, since `ppname_t`, say, is
`Sealed.sealed string` behind two abbreviations.

The normalization has to be interleaved with loading.  An abbreviation whose
module the run has not loaded does not unfold, and the failure is *silent*: the
type merely looks abstract, and the embedding for it merely looks missing.
Nothing has asked for these modules --- the type of a plugin's argument is not
something the demand-driven loop looks at --- so `RegEmb.whnf` loads the head's
module, unfolds, and repeats until the head stops changing.  Without this,
`FStar.Tactics.CheckLN.check_ln : term -> Tac bool` reports "no embedding for
`FStar.Tactics.NamedView.term`" for a `term` that is a bare abbreviation of one
the table does cover.

A type with no embedding is not fatal to the run: the plugin is skipped with
error 238 (`Warning_PluginNotImplemented`, as in the ML pipeline) and the
program is still emitted --- without a native implementation of that plugin.

**Generated embeddings.**  A `[@@plugin]` datatype has no `e_<name>` to find,
so one is generated: `RegEmb.embedding_for_datatype` builds an embedder that
matches on the value and rebuilds it as a term, and an unembedder that matches
on the term and rebuilds the value, and wraps the pair with
`mk_extracted_embedding`.  Like the registration itself (§13.1) this is emitted
as F\* syntax and handed to `Extract.expr_of_term`, so the constructors'
argument embeddings are found by the same `embedding_for` as everywhere else.

The one thing that is *not* ordinary F\* syntax is the recursion.  A datatype
refers to itself --- `pattern`'s `Pat_Cons` carries a list of `pattern`s ---
and the sub-embedding a constructor needs is a declaration that is still being
generated, which F\* syntax has no way to name.  So `embedding_for` answers with
a fresh **placeholder** variable, `RegEmb.compile` translates the term with the
placeholders in it, and then replaces each one by the declaration it stood for:
the embedding itself, or, when that embedding is part of the group currently
being built, an application of its **knot** `__knot_e_<name> : unit -> ...`.

That replacement has to be a *substitution*, and this is the subtle part.  The
first implementation abstracted the term over its placeholders and applied the
resulting lambda to the arguments, which is the same thing denotationally and
prints as `let x = __knot_e_pattern () in ...`.  The occurrences the generator
wrote are inside the embedder and unembedder closures, which run only once
there is a value in hand; a `let` hoists the call *out* of them, so the knots
of a recursive group call each other at module-initialization time and diverge
before any closure is built.  The Custard-built compiler allocated for nine
gigabytes and never printed its version.  Substituting in place leaves each
occurrence where it was written, and the recursion is tied by the closure, as
it is in the ML pipeline.  `RegEmb.subst_expr` is the traversal; it needs no
capture check, since a placeholder is a fresh name and what replaces it
mentions only top-level declarations.

#### What is not generated: a polymorphic plugin

A plugin with a leading type binder is *rejected*, with the same
"can not run natively" warning the ML pipeline uses, rather than registered.
The ML pipeline handles it by embedding the type variable with `mk_any_emb`
and pattern-matching the type arguments off the front of the `args` list, and
Custard could do the same: it would be a match wrapped around the lambda
`interp_term` already builds, peeling one argument per type binder.

It has not been built, and the reason is a measurement rather than a
difficulty.  Of the 163 `[@@plugin]` declarations in `ulib` and `src`, **none**
is polymorphic, and a full `make custard` --- which registers all 25 ulib
plugin modules --- emits no such warning at all.  Building `mk_any_emb`
support now would be machinery with no caller, and a registration that
unembeds at the wrong type is exactly the kind of silent wrongness §13.5 is
about.  The rejection is the honest answer until something needs it.


### 13.5 What it took to run

A Custard-built compiler that merely *links* proves less than it looks like.
Between linking and running the acceptance test --- a source file that declares
a typeclass, which exercises the `FStar.Tactics.Typeclasses` plugin end to end
--- were five bugs, and four of them were miscompilations that a smaller test
could not have reached.

- **An absurd postcondition erased a call.**
  `FStar.Stubs.Tactics.V2.Builtins.raise` is `raise_core e; ()`, which
  typechecks only because `raise_core`'s postcondition is `False`.  Extracted
  literally, the `()` is the value of the function and the raise is dead.  The
  general shape is "code after a call that never returns", and the general
  answer is that such code is unreachable: `Prims.magic` and `Prims.admit` now
  extract as `EAbort`, which prints as `failwith`, exactly as
  `Pulse.Lib.Dv.unreachable` already did, and `raise` is written
  `raise_core e; magic ()`.
- **Static quotations extracted as `()`.**  `Tm_quoted` was handled in
  `key_of_term` but not in `expr_of_term`, where it fell into the catch-all.
  A `Quote_static` is now embedded as a term view and rebuilt with `pack_ln`,
  with antiquotations resolved from `lookup_aq`, mirroring
  `FStarC.Extraction.ML.Term`; a `Quote_dynamic` is an `EAbort`.
- **A primitive step answered with a value that has no syntax.**  This is the
  important one.  `FStarC.TypeChecker.Primops.Docs` implements
  `FStar.Pprint.arbitrary_string` natively and `Primops.Errors.Msg` does the
  same for `text` and `mkmsg`, so `mkmsg "..."` normalized to an embedded
  `document` --- a `Tm_lazy` holding an OCaml object --- and was emitted as
  `()`.  Every error message in the compiler was an empty list.  Two rules come
  out of it, and both are now enforced:

  > A reduction whose reduct will be *compiled* must not run a primitive step
  > that can answer with a value having no term representation.  A reduction
  > whose reduct is only *printed* --- a specialization key --- may.

  The mechanism is a `unrepresentable_result` flag on `primitive_step`, set for
  those two groups (which stay enabled, because `text` and `mkmsg` are `val`s
  in the library interface and a tactic has no other way to evaluate them), and
  a new normalization step `Env.SafePrimops` which is `Primops` minus them.
  Custard's `custard_norm_steps` and `subst_norm_steps` ask for `SafePrimops`;
  `key_norm_steps` asks for `Primops`.  Turning primops off wholesale, which
  was the first fix, is *not* good enough: it stops an integer literal from
  folding to a literal and stops `tests/custard/Unroll.fst` from terminating.

  > Silence is the failure mode to design against.  Emitting `()` for an
  > unrepresentable value produces a program that typechecks and is wrong.

  So `expr_of_term` now has an explicit `Tm_lazy` case: unfold once with
  `U.unfold_lazy`, which is what turns an embedded `fv` back into the
  `pack_fv [...]` that rebuilds it, and otherwise raise error 369,
  `Error_CustardUnrepresentableValue`.  It caught a second instance the moment
  it was added.
- **A local `let rec` in `Tac` code was extracted as pure.**  `expr_of_term`'s
  `Tm_abs` case is the only place §7.5 reification happens, and `lift_letrec`
  peels the lambda itself with `U.abs_formals`, so the body it translated was
  never reified.  `FStar.Tactics.Typeclasses.extract_fundeps__aux` came out
  with a pure signature and a body that matched a tuple against a closure.  The
  rule: **any path that peels a lambda itself must reify explicitly.**
  `lift_letrec` now reifies against the residual effect and computes its result
  type through `Effects.reify_comp`, which is what `extract_letbinding` already
  did at the top level.
- **The generated embedding knots recursed eagerly**, described in §13.4.

A sixth turned up when the plugin of §12.12 was loaded and reduced nothing:

- **A stateful top-level value was eta-expanded.**  §3.2c specializes by
  applying a definition to a spine and re-abstracting over what is left, which
  copes uniformly with definitions that are eta-short or that are not
  syntactically lambdas at all.  But applying and re-abstracting *is*
  eta-expansion, and eta-expansion only preserves meaning when reaching the
  lambda is pure.  `FStarC.TypeChecker.Cfg.cached_steps` is the
  counterexample:

  ```fstar
  let cached_steps : unit -> ML prim_step_set =
      let memo = mk_ref (empty_prim_steps ()) in
      fun () -> if !extendable_primops_dirty then (...; memo := steps; steps)
                else !memo
  ```

  The `ref` is allocated once, when the module is initialized, and every call
  shares it.  Eta-expanded to `fun x -> (let memo = ... in fun () -> ...) x`
  it is allocated per call: the first call clears `extendable_primops_dirty`
  and every later one reads an empty table.  The Custard-built compiler folded
  *no* primitive step at all --- `1 + 123` did not reduce --- which is also
  why the plugin appeared not to run.

  > A definition may only be applied to a spine it did not ask for if it is a
  > value.  Everything else is emitted the way it was written.

  `specialize` now cuts the spine at the definition's own lambdas unless the
  definition is a value (`eta_safe`: a lambda, a name, a constant, a type),
  and the residual arrow becomes the declaration's result type --- so
  `cached_steps` comes out as a value of function type and its callers apply
  it, which is what the source said.  A `Mono` argument past the cut still
  forces the application, since there is no other way to specialize on it.
  `tests/custard/Thunk.fst` is a counter that prints `123` if the reference
  is shared and `111` if it is not.

| M | Deliverable | Notes |
| --- | --- | --- |
| M0 | `src/custard/` skeleton, `--codegen Custard`, `--custard_entry`, IR types, IR pretty-printer | No extraction yet; `--custard_dump_ir` on an empty program |
| M1 | Extraction loop for pure, first-order, monomorphic code; on-demand loading incl. `.fst.checked` preference (§4.2); ML backend | Enough to extract `let main () = print_string "hi"` |
| M2 | Type-class monomorphization (§3.1 rules 1,2,5) + `[@@monomorphize]` (rule 3); rejection diagnostics of §3.2; fuel (§3.6); key canonicalization (§3.7) | The two §3 examples pass as golden tests; `--custard_dump_specializations` for tuning |
| M3 | Layout analysis: erasure + uniform newtype collapse (§5.0) + cast elimination (§5) | Differential tests vs ML extraction |
| M4 | Effect classification + `extract_as_impure_effect` + purity discipline (§7) | Required before any Pulse code can be extracted.  `FStarC.Custard.Effects` and `FStarC.Custard.Simplify` |
| M5 | Krml backend + hardcoded builtin rules (machine ints, Pulse ops) | Done. M5a is `FStarC.Custard.Builtins` (§8.2); M5b is `FStarC.Custard.PrintKrml` behind `--custard_backend Krml` (§6), with the karamel AST split out into `FStarC.Extraction.KrmlAst`.  `tests/custard/KrmlBasic.fst` goes all the way to a compiled and executed C binary |
| M6a | Output polish: per-specialization suffixes, projector/discriminator inlining, externals printed at their uses, OCaml type annotations, `--custard_entry` vs `--custard_main` | Done. `tests/custard/Library.fst` covers the root-only (no `main`) mode |
| M6 | Registrable custom rules from plugins; Pulse moves off hardcoding | Done. `register_pre_rule`/`register_post_rule` in `FStarC.Custard.Builtins` (§8, phase 2) and the `[@@custard_extern]`/`[@@custard_c_header]`/`[@@custard_opaque]` source attributes (phase 3), tested by `tests/custard/Externs.fst` |
| M6b | Pulse: `[@@extract_as]`, `TBuf`/`EAny`/`EAbort` and the buffer operations, the Pulse rule table, `FStar.SizeT` (§8.3) | Done. `tests/custard/pulse/PulseBasic.fst` and `PulseHashTable.fst` both go to compiled OCaml and to compiled C; requires stage3, so neither is part of `tests/custard` |
| M6c | Bundled combinators (§3.9): weak-HNF substitution (§3.7), over-applied inlining and iota (§6 pass 5) | Done. `tests/custard/Combinators.fst`, extracted, compiled and run |
| M6d | Mutual recursion (§6 pass 8): `Simplify.scc` and `and`-grouping in the OCaml backend | Done. `tests/custard/Mutual.fst` |
| M6e | ANF (§6 pass 1): `Simplify.anf`, plus effect precision for externals (§7.3) | Done. `tests/custard/Anf.fst` |
| M6f | Unused-parameter elimination (§6 pass 7): `Simplify.unused_params` | Done, then **removed** by M10f: the optimization was a whole-program decision about a type's arity, which §5.5's principle forbids, and it bought nothing (`erased` covers the case).  `tests/custard/Phantom.fst` now asserts that a phantom parameter survives uniformly |
| M6g | Deleting unit-shaped proof binders (§3.1, §5.1): `Mono.keep_thunk` | Done. `tests/custard/Implicits.fst` covers both halves of the guard |
| M6h | `--custard_warn_any` (§5.9); §5.4 rule 3 measured unnecessary | Done. Escalated to an error over the whole corpus; `tests/custard/WarnAny.fst` is the positive test |
| M6i | Short-circuiting `&&`/`\|\|` (§6 pass 1): infix emission, bitwise guard | Done. `tests/custard/ShortCircuit.fst`, and the C side in `KrmlBasic.fst` |
| M7 | v2 monomorphization: infer-and-promote (§3.2b), defunctionalized function arguments (§3.8) | |
| M8a | Type monomorphization: one declaration per instantiation (§5.0.1), which unlocks per-instantiation layouts | `MonoTypes`; whole corpus re-run under the flag |
| M8b | Direct-to-C backend (§6): self-contained C11, no krmllib, function pointers but no closures | `KrmlBasic` and both Pulse modules compiled `-Wall -Wextra -Werror` and run; `CNoInt`/`CNoClosure` reject |
| M8c | Inline constructor fields (§5.7): `Simplify.inline_fields`, `TInline`, `[@@@custard_inline_field]` | Done. `tests/custard/InlineFields.fst`; closes the `\| Bar of a & b` indirection of FStarLang/FStar#4382 |
| M9a | An α-canonical, fully qualified, printer-independent key printer, replacing `show t` in `Extract.string_of_key` (§12.3) | Done. `Extract.key_of_term`; `tests/custard/KeyNames.fst`, which used to print `abab` |
| M9b | Exceptions (§8.5): `TExn`, the `DExn` producer, `raise`/`try_with` rules | Done. `tests/custard/Exceptions.fst`; OCaml only |
| M9c | `FStar.All`/`FStarC.Effect` reference rules (§8.4) | Done. `Builtins.ref_rule`; `tests/custard/Refs.fst`. OCaml only: a GC'd reference has no C representation |
| M9d | Measure §3.2b rejections over one real compiler module (§12.8 item 5) | Done. `FStarC.Syntax.Print.term_to_string` extracts whole; `FStarC.Main.main` stops at `Class.Ord.sort_by`.  Conclusion in §12.8 item 5: M7 is a prerequisite, and handles the common case but not all of it.  Found and fixed on the way: three loader bugs, a `Normalize` scope bug, local `let rec` extracting as `()` (§5.10), local functions blocking specialization (§5.11), an inline marker escaping newtype collapse (§5.2), and keys not seeing through local `let`s (§3.2b).  Also found: §5.11 must be restricted to polymorphic locals or extraction blows up exponentially (§12.8 item 8), and `Primops.Sealed.ops` builds a dictionary from a runtime value, which motivated §3.2c |
| M9f | Tell an effectful `Mono` argument apart from a runtime parameter (§3.2c) | Done. `Extract.effletdefs`; `tests/custard/MonoEffect.fst`.  Motivated by `Syntax.VisitM.tie_bu`, whose recursive `lvm` instance is tied through a `ref`, so no annotation and no restructuring of the source can make it static.  It is the identity-skeleton end of §3.2c -- dictionary passing -- and so wants the opt-in gate opened rather than a new mechanism |
| M9i | Weak-normalize specialization keys | Done. `TcEnv.Weak` in `key_norm_steps`.  Strong normalization of a key does not terminate whenever the argument is an instance whose method is recursive: reduction goes under the method's lambda, into `match` branches whose scrutinee is a bound variable and so cannot fire, and unfolds the recursion in each of them without bound.  `Class.Binders.hasNames_term` -- key term: the single fvar `hasNames_term` -- was still going after 500M steps and fifty minutes.  Cost: arguments differing only inside a lambda no longer share a specialization, which duplicates code but does not miscompile |
| M9h | Apply `dyn` to `Syntax.VisitM.tie_bu` | Done. Seven `dyn`s in `tie_bu`; the compiler still bootstraps and `--custard_entry FStarC.Syntax.VisitM.visitM_term_univs` no longer stops there.  `FStarC.Main.main` is back to the M7 blocker (`Class.Ord.sort`'s type parameter), which `dyn` cannot help with and no longer claims to |
| M9g | Call-site opt-in to the identity skeleton (§3.2c1) | Done. `FStar.Custard.dyn` in ulib, `no_specialize` blocked from unfolding via `DontUnfoldAttr`, erased by a `Rule_prim` in `Custard.Builtins`; `tests/custard/MonoDyn.fst`.  No change to `split_mono_args` or `check_mono_arg` was needed, which is the concrete payoff of §3.2c's "hole abstraction and dictionary passing are one mechanism": the marker merely turns the whole argument into a hole.  Known wart: `dyn` must wrap a pure term, since F\*'s ANF phase buries it otherwise |
| M9e | §3.2c hole abstraction: specialize on a `Mono` argument's skeleton, pass its runtime leaves as parameters | Done. `Extract.mono_holes`/`split_mono_args`/`specialize`, `sk_holes` in the key; `tests/custard/MonoHoles.fst` covers the dictionary and the closure case.  Unblocks `Primops.Sealed.ops`; subsumes closure arguments, which §3.2 had expected to need a separate defunctionalization pass.  Found and fixed on the way: `Sig_inductive_typ` parameters were used unopened, so a dependent parameter (`{| monoid m |}` after `m:Type`) crashed the normalizer, and constructor applications and patterns dropped only *erased* parameters while the type declaration dropped *all* of them, so a typeclass-parameterized inductive got the wrong constructor arity (`tests/custard/DepParams.fst`) |
| M9j | Fix the normalizer's `when`-clause scope bug | Done. `Normalize.matches`.  On a definite match against a branch with a `when` clause, the reduction was turned into `if w then <this branch> else match scrutinee with <remaining branches>` and the *whole* term normalized in an environment already extended with this branch's pattern bindings.  The remaining branches are closed with respect to the environment *before* that extension, so every de Bruijn index in them was read `\|s\|` slots too shallow; a second guarded wildcard branch therefore resolved its references to the first branch's binder.  `SMTEncoding.EncodeTerm.encode_term` hit it as `Failure("Term variable not found")` -- `env` wanted at slot 13, present at 14, after two `_ when ...` branches each pushing one binding.  Fixed by deciding the guard in place when the pattern binds something: reduce to the branch if the guard is a constant, otherwise block the match, which never spans two environments.  A pre-existing bug, not a Custard one; Custard only reaches it because it normalizes whole applied definitions.  `tests/custard/MatchGuard.fst` covers `when` clauses, which the suite had no coverage of at all, but does not pin the bug: the small shapes never reach this reduction path |
| M9k | Do not reduce fixpoints when normalizing a definition body | Done. `TcEnv.Exclude TcEnv.Zeta` in `custard_norm_steps`.  Custard never wants a fixpoint reduced -- a local `let rec` is lambda-lifted (§5.10), a top-level one is reached by a request -- so unfolding one only duplicates code, and against an open argument need not terminate.  `SMTEncoding.Term.termToSmt` found it: its inner `let rec aux'` opens with `let aux = aux (depth + 1) in`, a *partial* application of the recursive knot, and every unfolding produces another one; the budget error's histogram was 66k repeats of normalizing that one `let`'s type and no fvar unfoldings at all.  A fully applied recursive call does not diverge, which is why §5.10's tests never caught it.  With `PureSubtermsWithinComputations` already set, excluding zeta selects the normalizer's "no fixpoint reduction" branch, which normalizes under the `let rec` and puts it back.  Note zeta is on by default in `Cfg` and has to be turned off with `Exclude`, not by omission |
| M9l | **`FStarC.Main.main` extracts whole** | Done. 113728 lines of OCaml from one entry point, no `TAny` and no generated `Obj.magic`.  The last two blockers were `Parser.AST.pp_list'`, the `sort_by` shape again -- a `pretty` dictionary built from a runtime function -- fixed with the same `[@@@monomorphize]` on the function, and the `--custard_fuel` default of 10000, sized for tests, which the compiler exceeds slightly; raised to 100000.  `--custard_max_specializations` remains the per-definition limit and is the one that catches a real runaway.  Extraction of the whole compiler was the M9 goal; what remains before the output can be *built* is §12's separate compilation and the `[@@custard_extern]` convention for the hand-written `.ml` realizations (§12.8 item 3) |
| M10a | The unit interface: `--custard_unit`, `--custard_link`, the `.cui` format, `Driver` emission (§12.2) | Done. `FStarC.Custard.Unit`, serialized with the same `Util.save_value_to_file` that stores a `.checked` file -- the IR is plain first-order data, and a hand-written printer and parser would be several hundred lines to keep in step with an IR still in flux for no benefit a version check does not already give.  `--custard_dump_cui` covers the case where a human wants to look.  The header records the backend and the layout-affecting options and a mismatch is an error, not a warning: two units built with different `--custard_monomorphize_types` settings lay their types out differently and the interface has no way to say so |
| M10b | `request` interception, the `Imported` flag and the pass guards (§12.4) | Done. `Extract.import`, a dozen lines at the one choke point: a request whose key a linked unit exports is answered by a reference, its body is never looked at, and the requests that body would have made are never made either.  The layout freeze is `Layout.run`'s `imports` argument, which *seeds* the erasure, layout and constructor tables and marks the seeds pinned, rather than skipping imported declarations -- uses of an imported type still have to be rewritten, by the upstream unit's decisions.  The `Simplify`-stage decisions are frozen separately: see M10f |
| M10c | Per-unit namespacing: an OCaml module per unit, a C symbol prefix (§12.7) | Done for OCaml.  A unit compiles to a module named after it and every reference to an import is qualified explicitly rather than brought into scope with `open`: §12.6 expects two sibling units to re-specialize the same upstream definition, and an `open` would make that clash silent and the choice positional.  An imported *value* needed no new machinery at all -- it is exactly an external whose target happens to be another generated module, so `PrintOCaml`'s existing `externals` table carries it.  Types, constructors and record fields needed a parallel table.  `--custard_backend C` and `Krml` reject `--custard_unit`/`--custard_link`: they need a header and a linker story they do not have yet |
| M10f | Make every type-representation decision a function of the type, so that every declaration is exportable | Done.  The `records` and `inline_fields` *decisions* moved into `Layout` (§5.5, §5.7) and reach `Simplify` as a `verdicts` table; the two passes became appliers that decide nothing.  What made this possible: a new `PRecord` in the IR (every backend has one), which removes `records`' surviving-pattern condition; the observation that `inline_fields`' blocked-field scan was unreachable, since `Extract` only ever emits `PWild`/`PVar`/`PConst`/`PCtor`; and deleting `unused_params`.  What made it necessary: dropping a reshaped type from the interface is not an escape hatch, because global variables and exceptions have nominal identity across units (§12.5).  `Driver.stable_types`, `imported_shapes` and `ti_pre` are gone, and so is `Error_CustardBadUnitInterface`'s reason to fire: `Syntax.verdicts`, `Layout.record_verdict`, `Layout.ctor_plans`, `Simplify.records`, `Simplify.inline_fields`; `tests/custard/SepLib.fst` |
| M10g | Realized modules (§8.2) | Done.  `Rule_realized` and the list in `Builtins`: a type of a hand-written-OCaml module keeps its declaration for its shape but is not emitted, and every reference to it, to its constructors and to its fields prints as the realization's own name.  `FStar.Pervasives.Native`'s `option` and tuples are part of it, which is what makes the whole-program output callable from the realizations at all; tuples print in OCaml's tuple syntax, since they have no constructor to name.  Four bugs the OCaml build of the extracted compiler exposed on the way: abstract types lost their arity, eta-contracted abbreviations (`type psmap = t`) dropped their arguments, `try_with`'s thunk binder was dropped rather than bound to `()`, and `FStar.All.exit` was compiled to OCaml's `exit` rather than the realization that narrows the `Z.t`.  §12.8 item 3 |
| M10h | Coercions at the `TAny` boundary (§5.4) | Done.  `Simplify.coerce_prog`, the last pass in the pipeline: a bidirectional walk that inserts an `ECast` exactly where a value crosses a *printed* boundary -- a declaration's binders and result, an external's type, a constructor's or record's field types -- whose declared type disagrees with what the value is.  Nowhere else: a node's own `ty` is believed only when it mentions no `TAny`, since `Extract` falls back to `TAny` as often for "not worked out" as for "no representation", and driving the pass off those was the first implementation, which magicked every application.  Two asymmetries make it work: a coercion *to* `TAny` is well-typed whatever the source, so it needs only that the term obviously has *some* representation; and a node that hands its expectation to its own result (`if`, `match`, `let`, `try`) is not asked again, which is what keeps a coercion off the `if` as well as inside each branch.  Unblocks §12.8 item 6 -- `FStarC.Class.Monad`, a class over `Type -> Type`, which neither the IR nor OCaml can name.  Also: `Layout.resolve` no longer expands a realized abbreviation (`FStar.Dyn.dyn`), unless it is `inline_for_extraction` (`FStarC.PSMap.psmap`).  `tests/custard/Magic.fst` |
| M10i | Output splitting (§12.9) | Done.  `--custard_split` writes one OCaml file per F\* source module instead of one file for the whole program, so that F\*'s hand-written realizations — fourteen of which reference modules Custard compiles — can sit between the pieces; OCaml compilation units must form a DAG, and a single file made them circular.  Still one whole-program run: no unit interface, no re-specialization, just a partition of the already-sorted declaration list.  `Split.run` gives each declaration the latest home, in F\*'s own module order, among its own module and those of everything it references, which is what relocates a specialization that outgrew its source module; `PrintOCaml` prints a declaration under its plain identifier when it is at home, which is the name the realizations spell, and reuses the `Imported` flag of M10c for every cross-file reference.  Two codegen bugs fixed behind it: a record field mentioning a type variable the type does not bind (`Layout.close_fields`), and a realization shadowed by its model, which §12.10 and M10j turned into the general rule.  The compiler splits into files that compile with the realizations in `ocamldep -sort` order; §12.10.  `tests/custard/SplitLo.fst`, `SplitMid.ml`, `SplitHi.fst` |
| M10j | A realization replaces its module's values (§8.2) | Done.  Where `src/ml` or `ulib/ml` holds a hand-written `.ml`, the F\* definitions in that module are a model, and a model that disagrees with the realization — `FStar.Dyn`'s `dyn` is `unit -> Dv value_type_bundle` in F\* and `Obj.t` in OCaml — is not something extraction may silently choose between.  Every `Sig_let` in a realized module becomes a `DExternal`; an incomplete realization is now a link error rather than a program running the model.  Exempted, because they are not models: projectors and discriminators, `inline_for_extraction` symbols (which in a realized module means the realization deliberately does not define them, as `FStarC.PSMap`'s `psmap_*` aliases do), type abbreviations, and the two modules whose realization defines no representation of its own (`Builtins.type_only_realized_modules`: `FStar.Pervasives`, which has no file, and `FStar.Pervasives.Native`, which is transparent over types Custard represents natively — and whose `fst`/`snd`, left external, would freeze `tuple2` and leave the C backend with no representation for it).  Externals gained `dx_typars` so that §3.2 instantiates a polymorphic realization's signature at the call site: without it one `let fst = Stdlib.fst` types every caller's result as `any`.  The cost, accepted: what a realization implements is no longer monomorphized |
| M10k | Advancing the extracted-compiler build (§12.10) | Done.  Five code-generation bugs: a retained *type* binder passed as a runtime argument (`Mono.keep_thunk`/`unit_binders`, now typed `unit` so no `Obj.magic` is generated); a lambda-lifted local not receiving the captures of the lifted locals it calls; a lambda-lifted local keeping its own generalized type binders as value parameters instead of `dl_typars`; an eta-contracted abbreviation (`uvars = FlatSet.t ctx_uvar` through `t = flat_set`) unfolded with its own parameter still free, in both `Layout.resolve` and `Monomorphize.unfold_cty`; and a definition whose declared type hides its arrows behind an abbreviation (`let get : st ctxt = fun s -> ...`).  A *type* can now be a `--custard_entry`, which is how a realization gets at an abbreviation Custard unfolds rather than emits: `Extract.run` flags a `DType` root and `Driver.check_entrypoints` no longer rejects an entry whose module the on-demand loader has not reached.  `tests/custard/PolyVal.fst` and `TypeEntry.fst` |
| M10l | **The extracted compiler builds and runs** (§12.10) | Done.  A Custard-extracted `fstar.exe` verifies `FStar.List.Tot.Properties` from source and reports the same errors as the dune-built one.  What it took beyond M10k: **module initializers** --- an effectful top-level `let` is a root, and every loaded module contributes its own (§4.4), without which `FStarC.Options`' `let _ = clear ()` never ran; a `--custard_entry` that names a *module*, the only way to reach `FStarC.Hooks`, which exists solely for its side effects; and six codegen bugs, each listed in §12.10: a `ref` printed as an array (`lettys` and abbreviation unfolding), `-1` erased to `()` because the normalizer returns it as a `Tm_lazy` embedding, load-order-dependent extraction (`lookup_lid_typ`), an under-abstracted abbreviation, two lambda-lifted binders collapsed into one because `lift_letrec` opened the definiens twice, and OCaml record expressions resolving to the wrong record type.  `tests/custard/Literals.fst`, `Mymon.fst`, `Patlift.fst` |
| M10m | **Build integration** (§12.11): `make custard`, `mk/custard.mk`, `src/custard/entrypoints.txt` | Done.  Builds a Custard-extracted `fstar.exe` into `stagec/` from a stage 2 compiler, driving `menhir --infer` against Custard's own interfaces rather than borrowing the dune build's answer, and generating `FStarC_Version.ml` itself because Custard mangles `_version` to `u__version`.  `make custard-smoke` runs it. |
| M10n | **Reification** (§7.5) and the `custard_no_monomorphize` class opt-out (§3.1) | Done.  `Tac` is compiled through `tac_repr a wp = ref_proofstate -> Dv a`, in `Effects.{is_reifiable,reify_comp,maybe_reify}` and three call sites in `Extract`; `tests/custard/Reify.fst`.  The opt-out is what makes `embedding` a runtime value again, which reification and plugin registration both need. |
| M10p | **Plugin registration** (§13) | Done.  `FStarC.Custard.RegEmb` generates the registration for a `[@@plugin]` in a module named by `--custard_entry`, and the `e_<name>` for a `[@@plugin]` datatype with it, as F\* syntax handed to `Extract.expr_of_term` rather than as IR (§13.1, §13.4).  All 25 ulib plugin modules are roots in `entrypoints.txt`, and the acceptance test --- a source file declaring a typeclass, checked by the Custard-built `fstar.exe` --- passes.  The recursion in a generated embedding is tied by *substituting* the sub-embedding into the closure that uses it, not by binding it: a `let` hoists the knot out of the closure and the group diverges during module initialization (§13.4).  Fallout in the shared machinery: `Parser.Dep.deps_of` now parses a file the dependency scan never reached (§13.3), and `Extract` normalizes a definition body, its result type and its reification under the binders the specialization kept --- `FStar.Tactics.Util.map : ('a -> Tac 'b) -> ...` reifies to a comp whose universe mentions `'b`, and the top-level environment does not bind it.  Four miscompilations that only a running compiler could expose are in §13.5, the first of them the rule that a reduction whose reduct will be compiled must not fold a primitive step with an unrepresentable result (`Env.SafePrimops`, error 369) |
| M10o | **The `FStar.Stubs.*` rename** (§8.2) | Done.  `Builtins.no_fstar_stubs`, applied in `Extract.name_of_lid`, so that a plugin's `FStar.Stubs.Tactics.Types.proofstate` and the compiler's `FStarC.Tactics.Types.proofstate` are one name.  Fallout: `solve` is now `inline_for_extraction` in its five copies (its `{| ev : a |}` binder made `#a` `Mono`, which §3.2b rejects once `embedding` is no longer specialized), and record ascription had to cover projections as well as record expressions (§5.5). |
| M10d | A Custard-compiled plugin linking against a Custard-compiled compiler (§12.8 item 4) | Done, and it is `make custard-plugin` (§12.12).  A `.cui` entry now records the *file* a declaration was emitted into (`ue_home`), not just the unit, because the compiler is built split; an import that carries one is folded into the printer's `homes` table, since an import from a split producer and a cross-file reference inside a split output are the same thing.  `Loader.ensure_loaded` registers a module's dependences before the module, which a plugin run needs and a whole-program run got for free.  The test reduces `irreducible` definitions with `norm [primops]`, so it fails without the plugin.  It exposed the sixth miscompilation of §13.5: specialization eta-expanded `Cfg.cached_steps`, reallocating its memo table per call, and the extracted compiler folded no primops at all |
| M10q | Cleanup: bounded normalization everywhere, target-native tuples and `option` | Done.  Every normalization Custard performs now runs under `--custard_norm_budget`, through `Extract.norm_bounded` or the new `Mono.norm_bounded` for the callers below the extractor; the four sites in `Mono` and `RegEmb` that did not were the last unbounded ones (§12.8 item 8).  And a realized type that the realization defines as an *alias* of a type the target already has is printed as that target type: `FStar.Pervasives.Native`'s `tupleN` in OCaml's tuple syntax and its `option` as OCaml's `option`, so that no Custard-generated line in the extracted compiler names `FStar_Pervasives_Native` (§8.2).  `fst`/`snd` are `inline_for_extraction` |
| M10e | Structural specialization suffixes over all `Mono` arguments (§12.3) | Output polish, independent of everything else |
