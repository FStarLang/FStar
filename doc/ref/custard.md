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
sections 4–9 describe the surrounding machinery; section 10 lists the open
questions that need answers before/while implementing; section 11 is the
proposed milestone breakdown.

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
  uniq: int;              // disambiguator: 0 for the unspecialized decl,
                          // >0 for the n-th specialization
}

type cty =
  | TVar     of ident
  | TArrow   of cty & eff & cty
  | TApp     of name & list cty      // named type, incl. arity-0
  | TTuple   of list cty
  | TUnit                            // the sole inhabited erased value
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
  | ERaise  of name & list expr
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
`<Module>_<id>__<k>` where `k` is the specialization index, with a
human-readable suffix appended when it is short and unambiguous
(`bar__string`, `loop_unrolling__10`).  This mirrors what karamel already does
in `karamel/lib/Monomorphization.ml`, including the fall back to a hash when
names get long.  Readability of these names is the *only* debugging aid we
provide (locations are an explicit non-goal, and no `spec_key ↦ name` side
table is needed), so the mangler should prefer the readable suffix and fall
back to a hash only when it genuinely has to.

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
6. Otherwise `Poly`.

`Mono` binders are removed from the specialized definition's signature and
replaced by their concrete arguments in the body.  `Poly` binders remain.

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

The *only* bad case is the one above: a value that exists only at runtime
reaching a `Mono` parameter.  The interesting instance of it is storing a
dictionary in a runtime data structure — a `ref (foo a)`, a dictionary read out
of a `Poly` list, a dictionary returned from a branch — and then trying to call
a method on it.  Supporting that would mean falling back to real
dictionary-passing for those call sites, which is a genuine performance cliff
and therefore must be **manual opt-in**, not inference.  Out of scope for v1;
v1 rejects, per option 1.

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

## 4. Driver and on-demand loading

Custard is invoked as

```
fstar.exe --codegen Custard --custard_entry Main.main [--custard_entry Foo.bar] \
          --custard_backend krml|ml|c -o out.krml Main.fst
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

`type foo a = { x: a; p: prop }` is still a newtype of `a` — that is uniform,
because `p` is erased at every instantiation.  `type foo a = { x: a; y: bool }`
stays a two-field struct at every instantiation, even `foo prop`.

The rule composes with §2.1 for free: the layout table is keyed by the
*specialized* type name (§2.3), and under `--custard_monomorphize_types` there
are no type variables left, so the uniformity rule vacuously permits maximal
precision.  One rule, two regimes: uniform compilation of types when they stay
polymorphic, per-instantiation layouts when everything is monomorphized.  There
is no middle setting in v1.

### 5.1 Erasure

A type is erased when it is non-informative.  The existing predicate is
`TcUtil.must_erase_for_extraction` (`src/typechecker/FStarC.TypeChecker.Util.fst:3283`)
→ `Normalize.non_info_norm` → `Env.non_informative`
(`src/typechecker/FStarC.TypeChecker.Env.fst:1080`), which covers `unit`,
`prop`, `squash`, `Ghost.erased`, and anything with the
`must_erase_for_extraction` attribute.  Custard reuses it verbatim, and adds
the *structural* closure:

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

### 5.3 The layout fixpoint

Erasure and newtype collapse interact with the extraction loop: whether a
binder is dropped depends on whether its type is erased, which depends on the
type having been extracted.  The implementation splits this in two.

*Binder* erasure is decided during extraction (phase 2), where the F* type is
still available: `Mono.classify` gives a binder the class `Dropped` when
`TcUtil.must_erase_for_extraction` holds of its sort, and the argument is then
deleted at every call site by the same `split_mono_args` that handles `Mono`
arguments, so the two sides cannot drift apart.  One exception: a `unit` binder
is *not* dropped, even though `unit` is non-informative, because dropping the
`unit` parameter of an impure function would turn it into a value evaluated at
module initialization time.  Removing such thunks safely needs the effect
discipline of §7 and is left to a later milestone.

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

Rules 1 and 2 are implemented; rule 3 is not yet, and is only a matter of how
often rule 1 fires.

The goal is that `repr`-based programming (Pulse's `ref`s over erased indices,
`FStar.Ghost`, index-erasure idioms) costs literally nothing, and that any
surviving `ECast` is reported under `--custard_warn_any` as something a human
should look at.

### 5.5 Other representation choices (to be pinned down)

- Machine integers: `UInt32.t` etc. must map to native target types, not to
  their `nat`-refinement definitions.  Handled as custom rules (§8), the same
  way karamel does it today.
- `option`/`either`/tuples: `option t` where `t` is a pointer type is a
  candidate for null-pointer representation in the C backend.  Deferred.
- Refinement types are erased to their base type (they are already erased by
  the normalizer's `Unrefine`/`ForExtraction`).

---

## 6. Simplification and emission

Phase 4 passes, in order:

1. **ANF / let-normalization** (allowed by the non-goals).  This runs **first**,
   not last: every non-trivial subterm gets named and effect order becomes
   explicit, which is what makes the purity discipline of §7.3 tractable.  After
   ANF, every impure computation is a named `ELet` in a fixed order, so
   "may I reorder these?" is a question about statement order rather than about
   arbitrary subterm positions, and all the later rewrites operate on pure
   operands only.  It also happens to be what the C and Krml backends want.
2. **Erasure/newtype rewriting** (§5.1, §5.2).
3. **Coercion elimination** (§5.4).
4. **Dead-code elimination**: after monomorphization, reachability from the
   entrypoints is exact; drop unreachable decls (including class types whose
   dictionaries were all reduced away) and unused let-bindings whose effect is
   `E_Pure`/`E_Ghost`.
5. **Unused-parameter elimination** for the residual polymorphic decls.  The
   existing algorithm in
   `src/extraction/FStarC.Extraction.ML.RemoveUnusedParameters.fst` is a good
   template; Custard's version is simpler because it does not need to keep an
   ABI-compatible record of eliminated positions.
6. **SCC computation and topological sort** of the final decl list.

Emission:

- **Krml**: `FStarC.Custard.ToKrml` targets the same karamel AST as
  `src/extraction/FStarC.Extraction.Krml.fst`, writing the same
  `(version, files)` binary via `save_value_to_file` (cf.
  `Universal.fst:408`).  This is the first backend to build, because it gets us
  end-to-end C output with no new code generator.  Karamel's own
  monomorphization then has nothing left to do.
- **ML/OCaml**: `FStarC.Custard.ToML` produces the existing `mlmodule` and
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
- **C directly**: `FStarC.Custard.ToC`, last.  Because the program is
  monomorphic, ANF'd, and has explicit discriminators, this is a
  syntax-directed printer plus a struct/union layout decision for the residual
  `L_struct` variants.  "Pretty C" is an explicit non-goal.

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
| a user effect with `Extract_reify` | classify the reified computation |
| a user effect with `Extract_primitive` | `E_Impure` (see §7.2) |
| a user effect with `Extract_none` | hard error, if reachable |

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
| DCE a whole top-level `DLet` | always legal: top-level effects are not supported (`--warn_error -272` territory) |

"Hoist" means: replace the dropped argument `e` by an enclosing
`ELet (x, e.ty, e, ...)` so its effect still happens, in the right order, even
though its value is unused.  This is what makes erasing an argument of an
`E_Impure` call sound.

ANF is what makes this tractable, which is why it is phase 4's *first* pass
(§6): after ANF every impure computation is a named `ELet` in a fixed order, so
"reordering" is a question about statement order rather than about arbitrary
subterm positions, and every rewrite in the table above then operates on pure
operands only.

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

Effect-level behaviour (`extract_as_impure_effect`, effect classification, the
drop/dup/reorder discipline) is deliberately *not* part of this table; it lives
in §7, because it constrains the surrounding code rather than translating a
call.

### 8.2 Design

A single table, consulted in step 1 of the extraction loop:

```fstar
type rule =
  | Rule_prim   of (list cty -> list expr -> ST expr)   // build EOp/ECtor/...
  | Rule_type   of (list cty -> ST cty)
  | Rule_extern of { target_name: string; header: option string }
  | Rule_inline                                          // force unfolding

val register_rule : lid -> rule -> unit
val lookup_rule   : lid -> option rule
```

Phase 1: the table is populated by a hardcoded module
`FStarC.Custard.Builtins` covering machine integers, `FStar.Ghost`,
`FStar.Pervasives.Native`, and the Pulse primitives — as the draft says,
hardcoding is fine to start.

Phase 2: the table becomes registrable from F* plugins, using the same
mutable-ref/registration style already used by
`FStarC.Extraction.Krml.fst:617–712` (`ref_translate_type`,
`ref_translate_expr`, …) and `FStarC.Tactics.Native`.  Pulse then ships its own
rules instead of patching the compiler.

Phase 3 (optional, later): the rule can be *declared in F* source* via an
attribute, e.g. `[@@custard_prim "add32"]`, so that no OCaml plugin is needed
for the simple cases.

Types with custom rules are automatically exempt from erasure and newtype
collapse (§5.2), since their representation is fixed externally.

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
    and computing SCCs once the worklist is drained (§6, pass 6) is the plan.

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
5. **Which `option`/tuple representations to special-case** (§5.5), e.g. null
   pointers for `option t` in the C backend.
6. **CI coverage under demand-driven extraction** (§4.1) — accepted as expected
   behaviour, but the entrypoint set still has to be curated in practice.

---

## 12. Milestones

| M | Deliverable | Notes |
| --- | --- | --- |
| M0 | `src/custard/` skeleton, `--codegen Custard`, `--custard_entry`, IR types, IR pretty-printer | No extraction yet; `--custard_dump_ir` on an empty program |
| M1 | Extraction loop for pure, first-order, monomorphic code; on-demand loading incl. `.fst.checked` preference (§4.2); ML backend | Enough to extract `let main () = print_string "hi"` |
| M2 | Type-class monomorphization (§3.1 rules 1,2,5) + `[@@monomorphize]` (rule 3); rejection diagnostics of §3.2; fuel (§3.6); key canonicalization (§3.7) | The two §3 examples pass as golden tests; `--custard_dump_specializations` for tuning |
| M3 | Layout analysis: erasure + uniform newtype collapse (§5.0) + cast elimination (§5) | Differential tests vs ML extraction |
| M4 | Effect classification + `extract_as_impure_effect` + purity discipline (§7) | Required before any Pulse code can be extracted |
| M5 | Krml backend + hardcoded builtin rules (machine ints, Pulse ops) | End-to-end C via karamel; the sorting-typeclass benchmark |
| M6 | Registrable custom rules from plugins; Pulse moves off hardcoding | |
| M7 | v2 monomorphization: infer-and-promote (§3.2b), defunctionalized function arguments (§3.8) | |
| M8 | Direct-to-C backend; `--custard_monomorphize_types` (which also unlocks per-instantiation layouts, §5.0) | Only after M5 proves the IR is adequate |
