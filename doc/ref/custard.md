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

The only remaining producer of `ECast` is the machine-integer rules in
`Builtins`, and those are not lost information at all: they are the conversion
the source asked for, a real call into `FStar.Int.Cast`.  Rule 1 must not
delete them, and rule 3 could only duplicate them across branches.

`--custard_warn_any` (§5.8) is what turns "we measured zero" into something
that stays true.

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

The same pass replaces `EDiscrim (e, C)` on a one-constructor type by `true`
when `e` is pure.  That is worth doing on its own — the OCaml backend prints a
discriminator as a whole `match` — but it also matters for the second half,
which cannot fire while a discriminator still names the constructor.

**The conversion.**  A one-constructor type with at least one field, and with
no `PCtor` mentioning it left anywhere, becomes a `TRecord`; its `ECtor`
becomes an `ERecord`.  The IR has no record *pattern*, which is why the
surviving-`PCtor` condition is needed: a type that is still matched somewhere
has to stay a variant.

That condition is also why `depat` cannot simply project everything it can.  A
type may be matched irrefutably in one place and refutably (a guard, or an
extra `_` branch) in another; projecting the first while the second keeps the
type a variant would leave an `EProj` out of a variant, which the OCaml backend
prints as `e.f` and OCaml rejects.  So the set of blocked constructors is
computed *before* `depat` runs, counting only the patterns `depat` will not
consume, and `depat` skips the rest.

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

### 5.7 Other representation choices (to be pinned down)

- Machine integers: `UInt32.t` etc. must map to native target types, not to
  their `nat`-refinement definitions.  Handled as custom rules (§8), the same
  way karamel does it today.
- `option`/`either`/tuples: `option t` where `t` is a pointer type is a
  candidate for null-pointer representation in the C backend.  Deferred.
- Refinement types are erased to their base type (they are already erased by
  the normalizer's `Unrefine`/`ForExtraction`).

### 5.8 `--custard_warn_any`

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
7. **Unused-parameter elimination** (`Simplify.unused_params`).
   Monomorphization removes the type parameters a declaration is specialized
   on, but §5.0's uniform compilation deliberately leaves the `Poly` ones
   behind, and some of those describe nothing about the runtime
   representation:

   ```fstar
   noeq type tagged (a:Type) (ph:Type) = | L : a -> tagged a ph | R : a -> tagged a ph
   ```

   `ph` is a phantom: no field mentions it, so every instantiation of `tagged`
   has the same layout.  Carrying it costs nothing in OCaml, where the
   parameter is only a name, but the direct-to-C backend (M8) has to
   instantiate what it is given, so a phantom parameter there is a fork in the
   monomorphization for no reason.  It is also just noise in code that is meant
   to be read and checked in.

   "Used" is a *least* fixed point over the whole program, because a parameter
   can be used solely by being passed on: in `type chain (a:Type) (ph:Type) =
   tagged a ph`, `ph` occurs in the body, but only in a position of `tagged`
   that is itself about to be dropped.  Starting from "every parameter is
   unused" and only ever adding uses gets that right, and gets the recursive
   case right for the same reason — in `type t (a:Type) = ... t a ...`, a
   parameter that reaches nothing but the recursive occurrence really is
   unused.  A single pass in program order would settle the acyclic cases,
   since the program is topologically sorted by then, but a cycle has no such
   order, so the pass iterates.  The rewrite then drops the parameters and,
   at every use site, the `TApp` and `EQual` arguments at their positions.

   This is the analogue of
   `src/extraction/FStarC.Extraction.ML.RemoveUnusedParameters.fst`, which the
   ML pipeline needs to satisfy F#.  Custard's version is both simpler and more
   aggressive: because the program is whole, every use site is in hand, so
   there is no need to keep an ABI-compatible record of the eliminated
   positions for a separately compiled client to agree with, and the same
   analysis extends from type abbreviations to inductives and to the type
   parameters of functions.

   The pass runs between two rounds of dead-code elimination.  The first is
   what makes it precise — a use in a declaration that is about to be deleted
   is not a use — and the second collects the declarations that the rewrite
   itself orphaned, a type that was only ever mentioned in a phantom position.
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
  | `TAny` | the representation was already lost; `--custard_warn_any` (§5.8) says where |
  | `TTuple`, `ETuple`, `PTuple` | tuples must have reached the backend as `tupleN` inductives |
  | `POr`, pattern guards | no `EAbortS`-style approximation is available here |
  | `ERaise`, `ETry`, `DExn` | no exceptions |
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
changes the *term* Custard extracts, not the drop/duplicate/reorder question,
which is all `eff` is used for; Custard does not reify yet, and extracts a
reifiable effect through its representation type, which is what the ML pipeline
arrives at after reifying anyway.

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
| DCE a whole top-level `DLet` | always legal: top-level effects are not supported (`--warn_error -272` territory) |

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

`FStar.Ghost` and `FStar.Pervasives.Native` are not in the table: `Ghost` is
handled by erasure (§5.1) and the native tuples by `TTuple`/`ETuple`.  The
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

These are declared in `FStar.Attributes` and, unlike the table, are found by
*looking at the definition* rather than at its name, so `Extract` consults
`rule_of_attributes` separately — and lets it win over the built-in table, so
that a program can override a rule it does not like.  Note that
`FStarC.Syntax.Util.has_attribute` only matches a bare `fvar`; an attribute
that takes an argument has to be found with `get_attribute`.

Types with custom rules are automatically exempt from erasure and newtype
collapse (§5.2), since their representation is fixed externally.

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
| `Reference.alloc`, `Box.alloc` | `BufCreate LStack` / `BufCreate LHeap` of length 1 |
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

Three IR additions come with this: `TBuf` (§2.2), `EAny` for karamel's
`EAny`, and `EAbort of string` for `Pulse.Lib.Dv.unreachable` -- a `Dv`
function that Pulse emits where the proof says control never arrives.  It
prints as `failwith` in OCaml and as karamel's `EAbortS`.  In the karamel backend a `TBuf` is a real C pointer, so a Pulse `let
mut` scalarizes into a plain local and a `Vec.alloc` becomes
`KRML_HOST_MALLOC`.  In the OCaml backend a `TBuf t` is a `t array`; `BufSub`
has no OCaml representation and emits a `failwith`.  `FStar.SizeT` is a machine
integer width (`Sizet`) like the `FStar.UInt*` ones, with the usual conversion
rules.

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
5. **Which `option`/tuple representations to special-case** (§5.7), e.g. null
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
| M4 | Effect classification + `extract_as_impure_effect` + purity discipline (§7) | Required before any Pulse code can be extracted.  `FStarC.Custard.Effects` and `FStarC.Custard.Simplify` |
| M5 | Krml backend + hardcoded builtin rules (machine ints, Pulse ops) | Done. M5a is `FStarC.Custard.Builtins` (§8.2); M5b is `FStarC.Custard.PrintKrml` behind `--custard_backend Krml` (§6), with the karamel AST split out into `FStarC.Extraction.KrmlAst`.  `tests/custard/KrmlBasic.fst` goes all the way to a compiled and executed C binary |
| M6a | Output polish: per-specialization suffixes, projector/discriminator inlining, externals printed at their uses, OCaml type annotations, `--custard_entry` vs `--custard_main` | Done. `tests/custard/Library.fst` covers the root-only (no `main`) mode |
| M6 | Registrable custom rules from plugins; Pulse moves off hardcoding | Done. `register_pre_rule`/`register_post_rule` in `FStarC.Custard.Builtins` (§8, phase 2) and the `[@@custard_extern]`/`[@@custard_c_header]`/`[@@custard_opaque]` source attributes (phase 3), tested by `tests/custard/Externs.fst` |
| M6b | Pulse: `[@@extract_as]`, `TBuf`/`EAny`/`EAbort` and the buffer operations, the Pulse rule table, `FStar.SizeT` (§8.3) | Done. `tests/custard/pulse/PulseBasic.fst` and `PulseHashTable.fst` both go to compiled OCaml and to compiled C; requires stage3, so neither is part of `tests/custard` |
| M6c | Bundled combinators (§3.9): weak-HNF substitution (§3.7), over-applied inlining and iota (§6 pass 5) | Done. `tests/custard/Combinators.fst`, extracted, compiled and run |
| M6d | Mutual recursion (§6 pass 8): `Simplify.scc` and `and`-grouping in the OCaml backend | Done. `tests/custard/Mutual.fst` |
| M6e | ANF (§6 pass 1): `Simplify.anf`, plus effect precision for externals (§7.3) | Done. `tests/custard/Anf.fst` |
| M6f | Unused-parameter elimination (§6 pass 7): `Simplify.unused_params` | Done. `tests/custard/Phantom.fst` |
| M6g | Deleting unit-shaped proof binders (§3.1, §5.1): `Mono.keep_thunk` | Done. `tests/custard/Implicits.fst` covers both halves of the guard |
| M6h | `--custard_warn_any` (§5.8); §5.4 rule 3 measured unnecessary | Done. Escalated to an error over the whole corpus; `tests/custard/WarnAny.fst` is the positive test |
| M6i | Short-circuiting `&&`/`\|\|` (§6 pass 1): infix emission, bitwise guard | Done. `tests/custard/ShortCircuit.fst`, and the C side in `KrmlBasic.fst` |
| M7 | v2 monomorphization: infer-and-promote (§3.2b), defunctionalized function arguments (§3.8) | |
| M8a | Type monomorphization: one declaration per instantiation (§5.0.1), which unlocks per-instantiation layouts | `MonoTypes`; whole corpus re-run under the flag |
| M8b | Direct-to-C backend (§6): self-contained C11, no krmllib, function pointers but no closures | `KrmlBasic` and both Pulse modules compiled `-Wall -Wextra -Werror` and run; `CNoInt`/`CNoClosure` reject |
