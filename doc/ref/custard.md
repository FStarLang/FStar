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

This is *not* what §18.2 does, though it is what the EverParse report took it
for.  §18.2 is about an arity binder that was dropped and should not have
been; this note is about a parameter that is kept and cloned and need not be.
Both are still open in the second sense.

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
  | ECoerce of expr & cty                    // the *only* unsafe coercion node
  | ECast   of expr & cty                    // a machine-integer conversion
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
- **`ECoerce` replaces `MLE_Coerce` + `Obj.magic` + `FStar.Ghost.reveal`/`hide`
  + `admit`-style repr changes.**  It is `repr/magic built-in`.  Phase 4
  cancels `ECoerce (ECoerce (e, t1), t2)` and drops `ECoerce (e, t)` when
  `e.ty` and `t` have the same layout — which, after newtype collapse, is very
  often the case.  This is the "can be optimized away" requirement.
- **`ECast` is a different thing that happens to be spelled the same way in
  C.**  It is the machine-integer conversion of `FStar.Int.Cast` and
  `FStar.SizeT` (§8.1): it *computes*, so it fuses with nothing and is dropped
  only when the two widths are equal.  The two were one node until §17.2; see
  there for the miscompilation that cost.
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
4b. `b_i`'s type is an **inductive one of whose constructors stores a type**
   ⟹ `Mono` (§30.9).  `Mkbundle : (b_impl_type: Type0) -> (b_dflt:
   b_impl_type) -> bundle` is the shape: a value of such a type has no runtime
   representation, because its own contents decide what the representation is.
   Unlike rules 2 and 4 this is not a policy about what is worth specializing;
   the alternative is not a slower program but no program.  The inductive's own
   *parameters* do not count — `Cons : (a:Type) -> a -> list a -> list a`
   stores no type, and `list int` is an ordinary value.
5. **Dependency closure**: if `b_j` is `Mono` and `b_i` is free in the type of
   `b_j`, then `b_i` becomes `Mono`.  Iterate to a fixpoint (it terminates: the
   set only grows and is bounded by `n`).  This is the rule that makes `#a` in
   `bar #a {| foo a |}` monomorphized without annotation.
6. A **type binder** still `Poly` after the fixpoint of rule 5 ⟹ deleted.
   Under the uniform compilation of types (§5.0) a type argument cannot change
   any layout, so it has no runtime content.  This has to be applied *after*
   the fixpoint, so that rule 5 still gets the chance to promote it to `Mono`.
7. Otherwise `Poly`.
8. A **`Mono` binder nothing observable depends on** ⟹ `Dropped` (§30.14).
   Applied last, and only to `Mono`: a binder absent from the definition's
   body and from the *observable* part of the rest of its type -- refinements
   and computation pre-/postconditions removed -- cannot influence the output,
   and dropping it removes a specialization without changing a signature,
   since a `Mono` argument was never passed at run time.

**Opting a class out.**  Rule 2 says that a dictionary is known statically, and
for a type class that is what a type class is for.  But `tcclass` is also used
for things that are only *resolved* like classes and are otherwise perfectly
ordinary runtime values.  `FStarC.Syntax.Embeddings.Base.embedding` is the case
that forced the issue: an `embedding a` is a record of functions, built at run
time — `e_list e_sigelt` is a *call* — and passed around in lists and tables.
Made `Mono` it is unspecializable, and the extraction stops with error 364 at
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
- `--custard_entry_module` names a **module every top-level definition of
  which is a root**, which is what `--extract_module` means for the other
  backends.  It may be repeated.

`--custard_entry_module` is for the two cases where naming definitions one at
a time is the wrong shape.  One is a module compiled as a *library*, where the
program is whoever links against it rather than anything Custard can see.  The
other is a *test* of generated code (§15): a test module is a handful of
functions that exist to be looked at, and the property such a test needs is
that a function added to it is extracted without anyone having to remember to
name it.

It roots values only.  A type is rooted by the definitions that use it, and
under `--custard_monomorphize_types` a parametric type has no single instance
to root anyway.  A definition with nothing to extract --- a specification, a
proof, an `inline_for_extraction noextract` --- is passed over silently, unlike
`--custard_entry`, which reports one: naming a definition that extracts to
nothing is a mistake, while naming a module that holds some is not, because a
module normally holds specifications and proofs alongside its code.

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

   Not quite empty, as §31.3 records: a module realized by hand *in OCaml* is
   realized in C too as far as this pass is concerned, so `Prims.list` is
   frozen under the C backend by `FStar.List.Tot.Base`.  Error 368 now names
   the external that froze the type rather than claiming the pass missed it.

   A `Realized` or `Imported` *type declaration* is frozen for the same
   reason, and more directly.  Its representation is fixed outside this
   program — by the hand-written OCaml of §8.2, or by the unit that already
   compiled it — and it is not emitted here, so a clone of it would name a
   member that no module defines.  `FStar.Pervasives.Native`'s `option` and
   `tupleN` are the ones that matter: without this, `option int` asked for
   `FStar_Pervasives_Native.option__int`, which the realization has never
   heard of, and seven of the thirty-three modules in the test corpus failed
   to compile under the flag.  This half applies to the OCaml backend only,
   for the same reason the external half is empty in C: `Realized` records
   that a hand-written *OCaml* module defines the type, and the C backends
   link none of them and emit the declaration themselves.

   Being frozen affects the type's **name** and nothing else.  Its fields are
   still read back at the arguments the use site wrote, so `list int` inside a
   frozen `tuple2` is still cloned and a `[]` pattern under it still renamed
   to that clone's constructor.  Conflating the two — answering "no
   instantiation" for a frozen type and so losing its arguments as well as its
   name — left a subpattern matched at a bare type variable, which resolves
   nothing, so a constructor nested inside it kept its polymorphic name while
   its type was cloned out from under it.  Hence `Monomorphize.shape_of`,
   which answers what a type names, alongside `resolve_owner`, which answers
   whether it will be cloned.

Ordering costs nothing: the clones are appended at the end of the program,
because `Simplify.scc` topologically sorts the whole program — type
declarations included — at the end of phase 4, which is after this pass runs.

`tests/custard/MonoTypes.fst` is the test.  It asserts that two instantiations
of one type become two declarations, that a nested `list (list int)` works,
that an abbreviation and its expansion share a declaration, that no type
variable survives anywhere in the generated file, and that a frozen `option`
and `tuple2` keep their names while a `list int` inside the tuple does not.

Beyond that one module, the whole of `tests/custard` has been re-extracted
under the flag, compiled and run, and every module agrees with the output it
produces without it.

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
  so `unit -> ML (erased int)` is extracted normally.  The result type has to
  be *instantiated* with the call's own arguments before it is judged, or a
  polymorphic signature is judged on its variable: `Pulse.RuntimeUtils.magic :
  #a:Type -> unit -> GTot a` has result `a`, which is informative for all this
  test can tell, and a call to it survived into the output as a reference to a
  name no realization defines — it is `GTot`, so nothing was ever meant to.
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

`ECoerce` nodes come from three sources: source-level `Obj.magic`/`coerce_eq`,
`Ghost.reveal`/`hide`, and the subtyping mismatches that Custard itself
introduces (mostly around `TAny`).  Phase 4 runs:

1. `ECoerce (e, t)` → `e` when `layout t = layout e.ty` (after collapse);
2. `ECoerce (ECoerce (e, _), t)` → `ECoerce (e, t)`;
3. push coercions towards the leaves so that (1) fires more often.

Rules 1 and 2 are implemented, in `Layout.rw_expr`.  Rule 3 is **not
implemented, and as of M6h has nothing to bite on**: no `ECoerce` at all
survives to the backend, anywhere in the test corpus (all sixteen
`tests/custard` modules and both Pulse tests, including `PulseHashTable`, which
is exactly the `repr`-over-erased-index style this section is about).  The
generated OCaml corpus contains no `Obj.magic`.  That is the goal met, not a
gap, so rule 3 is deferred until an input demonstrates it is needed.

The reason is that two of the three sources above never reach phase 4:

- `Ghost.reveal` is `GTot`, so §5.1's erase-on-sight removes the call before it
  can become a cast.  (F\* will not even let you write a `Tot` wrapper around
  it.)
- `coerce_eq` extracts as an ordinary polymorphic identity function, which
  monomorphization then specializes and inlining then deletes.

The machine-integer rules in `Builtins` produce `ECast`, which is a *different
node* (§17.2) precisely so that none of the three rules can be applied to one
by accident.  A conversion is not lost information at all: it is what the
source asked for, a real call into `FStar.Int.Cast`.  Rule 1 would be sound on
it only when the two widths are equal, rule 2 never is, and rule 3 could only
duplicate it across branches.

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

**A boundary the pass cannot see is a boundary it will not insert at.**  This
is worth stating as a rule, because the failure mode is silent: a coercion is
simply not inserted, and the error appears in the OCaml output far from the
call.  Two ways it happened.

*An imported signature.*  `Simplify.run` is handed the declarations a linked
unit already compiled (§12.4) so that its passes can see their shape.  That
argument used to be filtered to types only — a type's layout is what
`ctor_infos` and `records` ask about — and the consequence was that a call to
an imported *function* found no signature at all and its argument and result
boundaries disappeared.  `FStarC.List.Tot.Base.map` returning `list 'b` into a
position expecting `list comp` is what surfaced it, in the Pulse checker
against `fstarc.cui`.  It is now the whole declaration list.

*A structured pattern under an `any` field.*  A coercion is an expression, and
a pattern is not, so `Mkdtuple5 (y, g1, (u_ty, ty_y), pre', k)` — matching a
pair against an `Obj.t` field — has nowhere to put one.  A pass `split_any`,
run just before `coerce_prog`, rewrites the field to a fresh variable and the
sub-pattern into an inner `match` on the coerced variable, where `coerce_prog`
can then do its job.  Branches with guards are left alone.

Two smaller boundaries in the same family.  A **comparison** is the one
operator whose operand types must agree with each other rather than with a
declaration, so when one side is `any` and the other is not, the `any` one is
coerced to the other's type.  And an **application head** that nothing
constrains and whose inferred type is `TAny` — `k`, the fifth field of a
realized `dtuple5`, applied as a function — is wrapped in a coercion to `TAny`
so that OCaml infers a function type for it rather than `Obj.t`.

The same head is a boundary in the other direction too.  When its type is not
trusted as a whole, each *parameter* of it that mentions no `any` is still the
best claim there is about that position, and an argument that arrives as `any`
has to be coerced to it.  The second component of a dependent pair is the
value that arrives that way: its type mentions the first, so the pair is
realized with an `any` field, and `let (| br, c |) = ... in ...` hands a `comp`
position an `Obj.t`.  Nothing else speaks for that argument --- the head is a
local closure, and a local closure's type is not printed, so OCaml infers it
from the body rather than believing Custard.  Pulse's `Pulse.Checker.If` is
the case that showed this up.

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
are the ones in the emitted file, and warns (code 367) about the two ways
Custard can lose track of what a value looks like at runtime:

- a **`TAny`** anywhere in a declaration's binder types, result type, `ELet`
  binding type, lambda binder types, record or variant field types, or external
  declaration type.  `TAny` is the analogue of the ML extraction's `MLTY_Top`;
  in a whole, monomorphic program there is almost always an answer, so an
  occurrence is a place something went wrong upstream.
- a surviving **`ECoerce`**.

One warning is emitted per declaration, listing its sites, rather than one per
occurrence: the IR has no source positions, so a flat list of anonymous
occurrences would be unusable.  The code is a `CWarning`, so `--warn_error @367`
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

That last is the honest answer only while `f` really is a *parameter*.  When
it is `Mono` — and rule 5 of §3.1 makes it so as soon as a `Mono` binder's
type mentions it, which for a `{| monad m |}` dictionary is always — the
instantiation is in hand and `f int` has a perfectly good spelling.  It was
still coming out as `any`, for a reason that shows up nowhere else: a
higher-kinded argument arrives as a **lambda**.  `specialize` substitutes it
with `SS.subst`, which does not reduce, so `m a` becomes
`(fun a -> ctxt -> ML (a & ctxt)) a` — a beta-redex whose head is a `Tm_abs`
rather than a name, in a position only `SS.subst` touched, because only the
definition *body* is normalized. `ty_of_typ` had no case for it and fell
through.

`FStarC.SMTEncoding.Pruning` is where this was noticed. Its scanning loop is
a state monad, `st a = ctxt -> ML (a & ctxt)`, written against
`FStarC.Class.Monad`; every `let!` in it was an `Obj.magic`, and every
signature said `Obj.t` where it meant `ctxt -> ('a * ctxt)`. Reducing the
redex — beta only, and only when the head really is a lambda, so each step
removes one and it cannot loop — takes the compiler's own extracted output
from **528 `Obj.magic` to 80** and from **21 `Obj.t` to 11**. What is left is
genuine: the `monad` and `lvm` *record types* are compiled once and are
uniform in `m` (§5.0), so their fields really are `Obj.t`, and
`FStarC.Syntax.VisitM`'s `lvm` dictionary is built at run time. The
regression is `tests/custard/MonoState.fst`.

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

   A fourth, and purely for the reader: **let-floating**
   (`Simplify.float_lets`).  ANF hoists every impure operand into a binding of
   its own, and an operand that was itself an application arrives already
   carrying the bindings *its* operands needed — so the definiens of a
   binding is very often another binding, and a body that was five
   applications deep came out as
   `let x = (let y = (let z = ... in ...) in ...) in ...`, nested as deep as
   the original expression.  That is the same program as
   `let z = ... in let y = ... in let x = ... in ...`: the bindings run in
   that order either way, and only the spelling differs.  The pass rewrites
   `ELet (x, ELet (y, a, b), c)` to `ELet (y, a, ELet (x, b, c))` and
   `ELet (x, ESeq (a, b), c)` to `ESeq (a, ELet (x, b, c))`, folded into
   `simpl`'s bottom-up descent so it reaches a fixed point for free.  It
   relies on variable names being unique within a definition, which the IR
   already guarantees (only *copying* a definition can break it, and `sub`
   renames when it copies): floating `y` outward extends its scope over the
   outer body, where a *different* `y` would be captured.  The C backend has
   always emitted the flat form, since C has no other; this gives OCaml the
   same.

   Three matching changes in the OCaml backend, which is where the result is
   read (`PrintOCaml.term`, `PrintOCaml.stmts`):

   - A run of bindings and statements is printed as **one sequence**: at one
     column, inside **one** pair of parentheses.  `let ... in` and `;` both
     extend as far right as they can in OCaml, so one pair around the whole
     run is as many as are needed, where a pair and an indentation step per
     element walked a long function off the right of the page and closed with
     a pile of a dozen brackets.
   - `ESeq` prints as `a; b` rather than `let _ = a in b`.  The discarded
     expression need not have type unit and OCaml warns about that, so one
     whose type is not `TUnit` goes through `ignore`.
   - A **record** — a type declaration or a literal — gets one field per
     line.  A literal that fits in `line_width` (80) columns where it already
     is stays on one line, since a two-field record of variables is not
     clearer for being spread over two.

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
  `--custard_backend KrmlC` (the default is `OCaml`); the output file defaults
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
- **C directly**: `FStarC.Custard.PrintC` (`--custard_backend C`) prints a C11
  header and a C11 source (§24) with no runtime of their own — the only
  headers are `<stdint.h>`, `<stdlib.h>`, `<stdbool.h>` and `<string.h>`, and
  the only definition the backend contributes is `typedef uint8_t
  custard_unit;`.  No krmllib, no macros: a generated file is meant to be
  readable, and to be compilable by any C11 compiler with nothing installed.
  "Pretty C" is still a non-goal; *warning-free* C is not, and the corpus
  compiles with `-Wall -Wextra -Werror`.

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
  guessing; error 368 names the enclosing declaration and says what to do.

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
| a user effect with `Extract_none` | hard error, if reachable (code 366) |

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
| drop a redundant `ECoerce` (§5.4) | always legal — `ECoerce` is pure |
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

A fourth source is the one that is easiest of all to get wrong: a call into a
recursion that is *still being extracted*.  Requests are depth-first, so a
callee's declaration is normally in `st.emitted` by the time a call to it is
translated --- and the exception is precisely a recursive call, whose
declaration cannot be there because it is the one being built.  Read as pure,
the first of the two calls in

```fstar
let rec walk (t:tree) : ML unit =
  match t with
  | Leaf n -> print_string (string_of_int n)
  | Node l r -> walk l; walk r
```

is a discarded pure subterm, and the table above deletes it: the traversal
compiles, and silently stops visiting half of its argument.  Nothing downstream
can notice.  This was a real bug, and it cost a day: it manifested as Pulse's
`--dep` output missing `FStar.Calc`, four levels of `scan_stmt` away.

So the fallback is `E_Impure`, and to keep it from costing anything,
`extract_letbinding` and the local-`let rec` case both register a
*provisional* declaration --- the real signature, a placeholder body ---
before extracting a body.  A self-recursive call then finds its exact effect
and its exact type (`callee_sig` had the same hole, and answered `TAny`).  A
call between two members of a mutually recursive top-level group is reached
through a request of its own and still falls back, which is sound and only
loses optimization.  `tests/custard/RecEffect.fst` is the regression, in all
three shapes.

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

*Over*-application is the mirror image, and §7.5 makes it the ordinary case
rather than a curiosity.  A `Tac` function extracts as a *pure* declaration
whose result type is the representation `ref_proofstate -> Dv a`, so a reified
call site supplies one argument more than the declaration has binders and the
effect that matters is the one on that last arrow.  `callee_eff` therefore
peels the surplus arguments off `dl_ret` with `apply_eff` and joins what it
finds there; reading `dl_eff` alone calls the whole call pure, and §7.3 then
deletes every tactic call whose result is discarded.
`FStar.Tactics.Typeclasses` is the case that showed this up: `__tcresolve`'s
`tcresolve' st0; debug ...` lost its first statement, so `tcresolve'` became
unreachable and was dropped as well, and the extracted compiler ran a
typeclass resolution that resolved nothing --- every `{| ... |}` argument in
ulib came back uninstantiated.

That case does, however, decide the definition's **result type**, and getting
it wrong is not subtle at all: each surplus binder consumes one arrow of the
declared result, and a result type that still contains those arrows describes
a function of higher arity than the one emitted.  The peeling has to run on
the *term*, unfolding as it goes, because an arrow can be hidden behind an
abbreviation, and behind another abbreviation past that one.  Pulse's prover
is the case that showed this up:

```fstar
type continuation_elaborator g ctxt g' ctxt' =
  post_hint_opt g -> st_typing_in_ctxt g' ctxt' post_hint ->
  T.Tac (st_typing_in_ctxt g ctxt post_hint)
let cont_elab g ps g' ps' =
  frame: list slprop_view -> continuation_elaborator g ... g' ...
let unreachable_elim (g: env) (goals: list slprop_view)
    : cont_elab g [IsUnreachable] g goals = fun frame post t -> ...
```

Three surplus binders, one arrow behind `cont_elab` and two more behind the
`continuation_elaborator` that unfolding it exposes.  Peeling the `cty`
instead cannot work: `ty_of_typ` emits an abbreviation *by name*, and a name is
not a `TArrow`, so the peel stops at the first one and leaves `unreachable_elim`
with five parameters and a result type that still promises two of them.

The term-level peel is not strictly stronger, so it falls back to the `cty`
one.  `FStar.Set.set a = restricted_t a (fun _ -> bool)` only becomes `a ->
bool` under a beta reduction *under* the binder, which only `ty_of_typ`'s own
higher-kinded-abbreviation unfolding (§5.0) performs; `FStar.Set.union`'s
declared result is `set a`, one arrow of which its fourth binder consumes.
`tests/custard/RetArity.fst` is the regression.

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

**A `reify` can get stuck on a `let rec`.**  `Effects.maybe_reify` puts the
marker on the body and normalizes; the normalizer discharges it by unfolding
the effect's `bind` and `return`, which works exactly when the term under the
marker is a monadic node.  A local `let rec` is not one.  Pulse's
`Pulse.Typing.Env` has

```fstar
  let rec pp1 (x : ...) : T.Tac ... = ... in
  T.Util.map pp1 tmp
```

and the `reify` sat in front of the `let rec` with nothing to reduce, so
everything after it — the whole body, including a call taking a proofstate —
was translated as if it were pure and the OCaml came out one argument short.
So `maybe_reify` pushes through a `let rec` structurally: open the group, push
its binders into the environment, reify the body, close it again.  The
definienda themselves are reified where they are extracted, by
`extract_letbinding`'s own lambda-lifting path.  `tests/custard/Reify.fst`'s
`after_letrec` is the regression.

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

Concretely, the rules fall into six kinds:

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
   `uintN_to_sizet` family map to the IR's `ECast`, which is a conversion and
   *not* the coercion node `ECoerce` (§17.2).
6. **Hand-declared types**: a type with no F\* definition whose layout the
   target fixes.  `[@@custard_extern]` on the declaration when the program
   owns it, `--custard_extern_type` when it does not; §14.5.

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
collapse and no inline-field expansion.

The record recovery of §5.5 still applies, but not unconditionally: for a
realized type the question is not what Custard would choose but what the
*source* said, because that is what a realization mirrors.
`FStarC.Parser.ParseIt.code_fragment` is `type t = { code; range }` in F\* and
a record in `FStarC_Parser_ParseIt.ml`; `FStar.Pervasives.dtuple3` is a
one-constructor inductive in F\* and a variant in `FStar_Pervasives.ml`.
Custard represents both as a `TVariant` and would normally make a record of
either, so the source's own shape is recorded on the declaration as a
`SourceRecord` flag, set from the `RecordType` qualifier, and
`Layout.record_verdict` reads it for a realized type instead of deciding.
Getting this wrong is not a warning but a type error at the far end: a
constructor pattern for an OCaml record, or a field label the realization
never declared.

The same distinction reaches `Simplify.irrefutable`, which turns a
single-constructor `match` into a field read (§5.5).  A realized *variant* has
no field to read, so it must keep its `match`; a realized *record* is a record
in OCaml too, its labels are the source's, and it projects like any other.

Two further things a realized declaration owns rather than Custard.  Its
**arity** is the realization's: `dtuple3`'s `b` and `c` are higher-kinded
binders, which §5.0 drops from a compiled type constructor because the
target's type language cannot hold them, but `FStar_Pervasives.dtuple3` takes
three parameters and a use that passed one would not name it.  So a realized
type keeps *every* type binder, writing the unrepresentable ones as `any`.
And the unfolding that recovers a higher-kinded *abbreviation* (§5.0,
`FStar.Set.set a = restricted_t a (fun _ -> bool)`) is for abbreviations only:
there is nothing to unfold in an inductive, and applying it to one made
`dtuple3` come out as `any`.

`tests/custard/Realized.fst` is the regression for all of this.

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
Compiling them is also what keeps `tuple2` monomorphizable in C: an external's
signature freezes the types in it (§5.0), and a frozen `tuple2` has no C
representation at all.  On the OCaml path `tuple2` is frozen regardless, by
the other half of that rule — it carries `Realized`, and OCaml's tuple is
what it must stay.

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

An exception is the one declaration that cannot be *duplicated*.  OCaml gives
each `exception` declaration its own identity, so a handler catches only the
one it was compiled against; two declarations that agree in name and payload
are two different exceptions.  This makes §8.2's stub mechanism sharper than it
is for anything else.  `no_fstar_stubs` rewrites a *namespace*
(`FStar.Stubs.Tactics.Common` to `FStarC.Tactics.Common`), which is enough
whenever the stub and its counterpart differ only there.  `Stop` is the
exception: the tactic engine's is `FStarC.Errors.Stop`, and `FStarC.Tactics.
Common` genuinely has no `Stop` at all, so the namespace rewrite resolves to
nothing and Custard emits a *second* declaration into a module of its own.  A
plugin built that way raises an exception the compiler it is loaded into cannot
catch, and the user sees the OCaml constructor name printed as an error
message.

So `Builtins.stub_aliases` is a table of whole-lident rewrites, consulted by
`Extract.unstub_lid` before `no_fstar_stubs`.  It has one entry, which is also
the only entry ML extraction's hard-coded equivalent has
(`UEnv.new_mlpath_of_lident`):

```fstar
let stub_aliases = [ "FStar.Stubs.Tactics.Common.Stop", "FStarC.Errors.Stop" ]
```

A missing entry is not a link error; it is a `.cmxs` that loads, runs, and
mishandles one control path.

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

Two exceptions to "everything the unit emitted".  The `Inline` declarations —
the projectors and discriminators that are substituted at their uses and never
emitted at all — are excluded, since exporting one would name a symbol that
does not exist.  A downstream unit re-derives them, which costs nothing.

And a `DExternal` is excluded, because it is a hole the unit *leaves* rather
than a symbol it provides.  A hand-written realization usually fills it — but
so, sometimes, does another Custard unit: Pulse's `checker` has its own copy
of `PulseSyntaxExtension.ASTBuilder.fsti` with no `.fst`, so `parse_pulse` is
an external there and a real definition in the `syntax_extension` unit.
Exporting it told `syntax_extension` the symbol was already compiled, and that
unit then skipped the very definition it was there to contribute; the link came
out with a reference and nothing to resolve it against.  A downstream unit
derives an external's signature from the source anyway, exactly as the upstream
one did, so nothing is lost.

Everything else is exported unconditionally, and §12.5 explains why that is
both possible and necessary.

### 12.3 The specialization key

Names do not need to be deterministic, and it would be a mistake to make the
design depend on their being so: two type-class instances for the same type
will always need a disambiguating subscript from somewhere.  The interface
records the **full emitted name**, and downstream reads it.  So
`spec_suffix`'s discovery-order counter (`Extract.spec_suffix`, `Extract.request`)
would be fine as it stands.  It is nonetheless worth not having: a name that
says only *when* a specialization was discovered is a name a reader has to
look up, and the output of this pipeline is meant to be read.

So the structural scheme `Monomorphize.request` already uses for types
(`Monomorphize.hint_of_cty`, which is what produces
`tuple3@tree_int_int_tree_int`) is folded over **all** the `Mono` arguments of
a value specialization, rather than the head symbol of the first
(`Extract.hint_of_term`, `Extract.hints_of`, `Extract.hint_of_args`).  A
`Mono` argument is an arbitrary term — a whole function body, in the §3.2
sense — so unlike a `cty` there is no bound on its depth and the recursion is
fuel-limited, at three levels.  Four rules do most of the work:

- A **constructed value is dropped** when a sibling argument had something to
  say.  Almost every one is a type-class dictionary, which is a function of
  the type it was built for — and that type is usually one of the siblings, so
  the constructor name only repeats it.  `Combinators.parse` specialized at
  `parser_combinator (t & t)` is `parse__tuple2_t_t`, not
  `parse__tuple2_t_t_Mkparser_combinator`.  It is kept when it is all there
  is, since a constructor name still beats a number.  The test is
  `TcEnv.lookup_sigelt` and `Sig_datacon?`; `fv.fv_qual` looks like the test
  and is not, being `None` for most data-constructor `fv`s.  It sees through
  the lambda §3.2c's hole abstraction wraps a skeleton in, since a dictionary
  with a runtime field is still a dictionary.
- Two arguments that **spell the same thing say it once**: `show__int`, not
  `show__int_int`.
- The hint is **cut to `hint_width` = 48 characters**, dropping components
  from the right, since the leftmost argument is the one a reader recognizes.
  The first component survives whatever its length, because a hint of nothing
  is worse than a long one.  Without this the compiler produced a
  225-character name of which the first 40 carried the content.
- A **lambda-lifted local inherits its enclosing definition's suffix**, the
  way `Monomorphize.with_spec` gives a constructor its type's.  It is one
  function per specialization of the definition it sits in, and numbering
  those by discovery order says nothing.  `st.cur` is set to the lifted name
  while its body is extracted, so a local nested in a local inherits in turn.

Dropping a component can make two hints collide, which is the case
`spec_suffix`'s `claim` already handled by appending the sequence number.

Measured over the compiler's own extracted output (`stagec/split/*.ml`, 1796
distinct mangled names): bare numeric suffixes fell from **243 to 121**, the
collision fallback from **409 to 204**, and the longest name from **225 to
100** characters.  What is left is mostly genuine — several distinct locals
called `aux` in one definition — or compiler-generated (`uu_`).

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

A key is a normal form, which means producing one substitutes away whatever
sharing the source had.  §30.17 is what that costs: a value that is small
only because it is shared cannot be specialized by value, and Custard falls
back to keying on the weak head normal form, or on the argument as written,
rather than failing.

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
   callers below the extractor.  Exceeding it is error 365, naming the term
   as written; `tests/custard/NormBudget.fst`.

   The two are not interchangeable and the split is not cosmetic: a budget is
   only useful if the message says *which* definition was being reduced.
   `Mono` is below the extractor and cannot ask it for the chain, so the
   extractor leaves a way to ask behind; see section 18.3.  Anything that
   normalizes and does have a chain directly should still use
   `Extract.norm_bounded`.

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
lists them one per line, `#` for comments, and `--custard_entrypoints` reads
the file --- the option exists so that the *format* is defined once, in the
compiler, rather than by a `sed` in the makefile.  Two kinds of line appear
there, and the file says which is which: a declaration that some hand-written
realization calls, which nothing in F\* refers to and demand-driven extraction
would otherwise drop (§12.9); and a bare *module* name, kept for its
initializers (§4.4).

The option may be repeated, and that is how a **plugin** contributes roots.
The compiler is a whole program, so it contains what its own entry points
reach and no more; a plugin's hand-written realizations call it by OCaml name,
through no request Custard can see, and those symbols have to be in the binary
the plugin is loaded into --- which is built before the plugin exists.  So the
plugin ships a file of them and the *compiler's* build reads it alongside its
own.  `pulse/src/custard-entrypoints.txt` is the first, and `mk/custard.mk`
names it directly, since this repository builds Pulse; another plugin's file
goes in `CUSTARD_ENTRYFILES`.

This is the whole-program assumption meeting a program that is not whole, and
it is not a defect to be designed away: it is the same bargain as a C or Rust
library exporting an explicit symbol list.  What it costs is that the set of
plugins is an input to the compiler's build.

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
   the entry file, into `stagec/split/` --- 222 files.
3. **Assemble.**  A dune project is *written* into `stagec/dune/`: a
   `dune-project`, a `wrapped false` library `fstarcompiler` whose sources are
   `stagec/split/`, `src/ml/` and `ulib/ml/plugin/`, and an executable whose
   only module is a two-line `zzMain.ml`.  The sources are symlinked
   directories rather than copies, so editing a realization does not re-run
   the extraction, and nothing overlaps: a realized module's F\* definitions
   are a model and Custard does not emit them (§8.2).  `FStarC_Version.ml` is
   generated by a rule in the project rather than copied from the dune build,
   because it assigns to `FStarC.Options`' `_version`, and Custard mangles a
   leading underscore to `u__` (§5.2) where the ML extraction does not.
4. **Compile.**  `dune build fstar-exe/zzMain.exe`.

Building this way rather than by hand is worth spelling out, because for a
long time it was done by hand.  The reason it looked as if it had to be was
the parsers.  `menhir --infer` types a grammar's semantic values by compiling
a mock module against the surrounding code, and the surrounding code here is
*Custard's* `FStarC_Parser_AST`, not the ML extraction's; borrowing the dune
build's answer would be relying on the two extractions happening to lay out
`FStarC.Parser.AST.term` the same way.  So the makefile drove menhir itself,
which needs `.cmi`s for everything the grammar's header opens --- and getting
those meant a best-effort `ocamlc -c` pass over every module in `ocamldep
-sort` order, ignoring failures.

But `--infer` against *this* library is exactly what a `menhir` stanza in a
dune project already does, and the stanza gets it right without the
best-effort pass, because dune knows the real dependency order.  So the
generated project has two `(menhir (modules ...))` stanzas and that is all.
What this bought is in §12.14: the hand-rolled menhir and link stages took
51 s and 78 s, both serial; the dune build takes 18 s.

Two details of the generated project are not obvious.

`(modes native)` and `(library_flags (-linkall))`.  `-linkall` is needed, for
the plugin registrations of §4.4, but it goes on the *library* and not on the
executable.  `fstar.lib` supplies `Prims`, `FStar_Pervasives` and the other
app-side realizations, so it has to be in `(libraries)`; it also contains an
`FStar_Order`, which Custard emits too.  With `-linkall` on the executable
that is a fatal *Duplicated implementations*; with it on the library, only
`fstarcompiler` is force-linked, `fstar.cmxa`'s `FStar_Order` is simply never
pulled in, and the collision does not arise.

`(env (_ (flags (:standard -w -A))))`, because generated code warns
constantly, and `(bin_annot false)`, because nothing reads the `.cmt`s.

Where dune leaves the artifacts matters to §12.12 and §12.13, which link
plugins against them.  It is
`stagec/dune/_build/default/fstar-guts/.fstarcompiler.objs/`, with the `.cmx`
and `.o` under `native/` but the `.cmi` under `byte/` --- so a plugin needs
`-I` for both.  `mk/custard.mk` calls that pair `$(INCS)`.  The filenames are
dune's own lowercase-initial ones (`fStarC_Main.cmx`), which OCaml resolves
without help.

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
3. `ocamlopt -shared` against the compiler's objects (`$(INCS)`, §12.11);
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


### 12.13 The Pulse plugin

`tests/custard/plugin` is a plugin written for the purpose.  The Pulse
checker is the real thing: 126 F\* files in three units, three `[@@plugin]`
declarations, four hand-written OCaml realizations, and a menhir grammar.
Pointing Custard at it is the honest measure of §12, and it has been done:
**all three units, linked against each other and against a Custard-built
compiler, compile to one loadable `.cmxs`, and that compiler checks the whole
of `pulse/test` --- 58 files, 58 pass.**

That is the end of the demonstration §12 was aiming at, and it is a make
target rather than a demonstration: `make custard-pulse-plugin`.

**What already works.**  `Pulse.Main` extracts whole against
`stagec/split/fstarc.cui`: one unit, 7.6k lines of OCaml, in about two
minutes.  `check_pulse`, the nine-argument monomorphic plugin, gets a correct
`register_tactic` with a fully spelled-out embedding for every argument,
including nested `e_tuple3`/`e_option`/`e_list` towers.  Nothing needed
teaching about Pulse: its realizations are `assume val`s under an interface
with no implementation, so §8.2's external mechanism picks them up without an
entry in `Builtins.realized_modules`.  And none of the four realizations
mentions a Pulse F\* module, so §12.9's output splitting is not needed here at
all --- the circularity that forced splitting on the compiler does not exist.

**One thing stops it.**  Two others are done.  The polymorphic plugin
`check_pulse_after_desugar (decl:'a)` is done: §13.4 now generates the
`mk_any_emb` registration for it, and `Pulse.Main` extracts with no
`--warn_error` suppression at all.  And every compiler symbol the
realizations name now resolves against a Custard-built compiler.

**How the realizations were made to resolve.**  A Custard-built compiler
contains what its own entry points reach, and no more; a plugin's
hand-written OCaml calls it by OCaml name, through no request Custard can
see.  §12.11's `--custard_entrypoints` is the answer, and
`pulse/src/custard-entrypoints.txt` now carries Pulse's list.  Six of the
seven symbols `Pulse_RuntimeUtils.ml` needed go in it and land:
`Errors.with_error_bound`, `Syntax.Compress.deep_compress_uvars`,
`TypeChecker.Normalize.unfold_whnf'`, `Syntax.Util.unlazy_as_t` and the two
`Syntax.Free` `ord` instances.  (Its other 68 references to the compiler
resolved already, and were only ever *thought* to be at risk: a scan that
does not strip OCaml comments reports symbols that appear in a commented-out
block.)

The seventh could not.  `FStarC.FlatSet.union` takes a typeclass dictionary,
and §3.1 classifies such a binder `Mono`, so it is specialized at each *call
site* --- and a root has no call site.  Custard makes the root's dictionary a
runtime parameter and then fails one level down, where `union` passes it to
`add`:

```
Error 364: The argument passed to the monomorphized binder number 0 of
FStarC.FlatSet.add is the runtime parameter a, so there is nothing to
specialize on.  Reached through: FStarC.FlatSet.union
```

This is not the entry-point mechanism failing.  It is the general question of
passing a `Poly` argument where a `Mono` binder is expected, which is a
performance cliff, was ruled out of v1 by design, and would need `add` and
everything below it compiled generically too.

The fix is the one the design already asks for: a `Mono` binder wants a call
site, so give it one.  `PulseSyntaxExtension.Env` --- a Pulse F\* module,
already built `--with_fstarc`, already named by `Pulse_RuntimeUtils.ml` ---
gained two three-line wrappers,

```fstar
open FStarC.Syntax.Free {} // the ord instances for uvars

let union_ctx_uvars (s1 s2 : FlatSet.t S.ctx_uvar) : ML (FlatSet.t S.ctx_uvar) =
  FStarC.FlatSet.union s1 s2
let union_univ_uvars (s1 s2 : FlatSet.t S.universe_uvar) : ML (FlatSet.t S.universe_uvar) =
  FStarC.FlatSet.union s1 s2
```

and the realization calls those.  Note the `open ... {}`, which imports
instances and nothing else: a `{| |}` binder cannot be supplied with
`#`-syntax, so the instance has to be *in scope* rather than passed (error
189, "Expected expression of type Type").  These are entry points of the
*plugin*, not of the compiler, so they are specialized where Custard can see
the type --- and in fact they specialize to code the compiler already has:

```ocaml
let union_ctx_uvars (s1 : FStarC_Syntax_Syntax.ctx_uvar list) =
  FStarC_Syntax_Unionfind.fStarC_Class_Setlike_union__ctx_uvar s1
```

So no entry point was needed for `union` after all, and this is the general
shape of the answer for any monomorphized compiler function a realization
wants: name it from F\*, at the type you mean, and call the wrapper.

With that, `PulseSyntaxExtension_Env.ml` and `Pulse_RuntimeUtils.ml` both
compile against the built compiler with no unresolved symbol.

#### The three-unit link

`checker` and `syntax_extension` are mutually dependent as F\* modules and
strictly ordered as Custard units.  `checker` extracts first, linked against
`stagec/split/fstarc.cui`; `syntax_extension` extracts second, linked against
both `fstarc.cui` and `PulseChecker.cui`.  That second link is visible in the
output: 33 generated `.ml` files become 13, the rest resolving through the
interface.  `extraction` is third and is the easy one: it depends on the
compiler and not on the other two units, so it links against `fstarc.cui`
alone and produces **three** `.ml` files for its 930 lines of F\* --- every
other module it mentions is the compiler's, and resolves through the
interface.  Its three modules are all roots, because the entire unit is
reachable only through top-level `let _ = register_pre_translate_*`
initializers (§4.4) and nothing calls into it by name.  The three
directories are then compiled together --- 85 generated files plus the four
realizations and the two menhir grammars --- into one 11.8 MB `.cmxs`.
`--infer-write-query`/`--infer-read-reply` handles the grammars
exactly as §12.11 does for the compiler's own parser; nothing about a plugin's
grammar needed new machinery.

Four things had to be got right, and each is a rule rather than a workaround.

**Two units cannot share one checked-file cache.**  `PulseSyntaxExtension.
ASTBuilder.fsti` and `Pulse.Main.fsti` exist in *both* units' source trees with
different contents, so `checker.checked` and `syntax_extension.checked` contain
different files of the same name.  Copying both into one directory silently
gives one unit the other's interface, and the failure is a hash mismatch a
long way from the cause.  `--debug CheckedFiles` prints `Differ at:
Expected …/Got …`, which is the only practical way to find it.  The same
applies to `--include`: `Find.full_include_path` is *cache dir, then library
paths, then include paths, then `.`*, and the **last** directory wins.

**A unit does not export its holes.**  See §12.2: `parse_pulse` is an external
in `checker` and a definition in `syntax_extension`, and exporting the external
made the definition disappear.

**A unit needs an `--include` for its own source directory.**  When its
modules have `.fsti`s, the checked file records an `("interface", ...)` hash;
without the include the `.fsti` is invisible, the hash has no counterpart, and
the module is reported "not checked" with no hint as to why.  `--debug
CheckedFiles` printing *Hashes computed (14)* against *Hashes read (15)* is
what identifies it.

**A cross-unit definition needs an entry point.**  Nothing *inside*
`syntax_extension` calls `parse_pulse` or `desugar_pulse`; only `Pulse.Main`,
in the other unit, does, and a call across a unit boundary is not a request
Custard can see.  So they go in
`pulse/src/syntax_extension/custard-entrypoints.txt` alongside the grammar's
constructors, for exactly the reason §12.11 gives.

#### Loading it

The `.cmxs` loads into `stagec/out/bin/fstar.exe` and checks Pulse programs.
Two caveats about *running* the Custard-built compiler, neither of them about
the plugin:

* It cannot read dune-built `.checked` files, and **segfaults** rather than
  erroring when handed one.  Always give it `--cache_checked_modules` and a
  fresh cache directory --- which is exactly what `mk/custard.mk`'s `smoke`
  target does, and why it says so.
* `cmd | tail` reports `tail`'s exit code, so a crash bisected through a
  pipeline looks like a success.  This wasted an afternoon and is recorded
  here so it does not waste a second one.

Getting from "loads" to "checks Pulse" took three bugs, and all three were in
the extractor rather than in §12:

1. `Pulse.Lib.Tactics` carries a `[@@plugin]` and was not a `--custard_entry`,
   so its tactic had no native implementation and got stuck (§13.3).
2. `FStar.Stubs.Tactics.Common.Stop` was duplicated into a module of its own,
   so the plugin raised an exception the compiler could not catch (§8.5).
3. A recursive call was assumed pure, so `§7.3` deleted the first of the two
   recursive calls in Pulse's `scan_stmt`, and the dependency scanner stopped
   traversing half of every statement (§7.3).

The third is the interesting one, and the argument for doing this exercise at
all: it is a *silent miscompilation*, it had been there since the beginning,
and no test in `tests/custard` --- nor any amount of reading --- had found it.
A 126-file program did, in a day.

#### `make custard-pulse-plugin`

The recipe is `mk/custard.mk`'s `pulse-plugin` target: three extractions, a
link, and a check of `pulse/test/CalcInPulse.fst` with the result loaded,
which is a Pulse program that exercises the parser, the checker and the
dependency scanner at once.  It depends on `pulse/build/*.checked`, so `make`
(or `make 3.full`) has to have run.  Each unit gets a cache of its own, built
from `stage2/ulib.checked`, `stage2/fstarc.checked`, the three `lib.*`
units and the unit's own checked files, in that order.

Two things about the checked files are worth writing down, because both cost
an hour and neither is about Custard.

`--include $(ULIB_CHECKED)` is needed by the `checker` unit.  Under
`--with_fstarc` the prelude is otherwise found in the *installed*
`fstarc/src.checked`, and those are the fstarc flavour of `Prims` and
`FStar.Pervasives`: their `fstar.prelude` and `fstar.reflection.typing` bundle
hashes are not the ones `Pulse.Main.fsti.checked` was written against.  What
this reports is Error 317 on `Pulse.Main.fsti`, with no mention of a prelude
anywhere; `--debug CheckedFiles` and its `Differ at:` lines are the only way
to see it.  Putting a copy in the cache does *not* help --- the cache is
searched first and the **last** hit wins.

`--already_cached '*,'` has to be the last such option on the command line,
since F\* keeps only the final setting.  An earlier `--already_cached
'Prims,FStar'`, which is what `pulse/mk`'s own `DEPFLAGS` would suggest, is
simply dead: that one belongs to a separate `--dep` invocation which this
build does not make.

#### What is left

1. **Nothing, for the plugin itself.**  The one realization whose names
   differ, `Pulse_Extract_CompilerLib.ml`, now has a Custard-flavoured copy in
   `pulse/src/ml-custard/`, which the link step overlays on `pulse/src/ml/`.
   (A *sibling* of `src/ml` and not a subdirectory of it: the dune build
   symlinks `src/ml` into an `include_subdirs unqualified` library, which
   would pick a subdirectory up as a second definition of the module.)
   The two differences are both about the record a constructor's payload
   becomes: ML extraction disambiguates field names across the whole module,
   so `Tm_meta`'s `tm` is `tm2` and `Tm_let`'s `body` is `body1`; and §5.7
   inlines the `letbindings` *pair* into the record that holds it, so one
   `lbs` field becomes `lbs` and `lbs1`.  This is the expected shape of the
   problem (§8.2): a realization is a contract with a *particular*
   extractor, there is no one file that satisfies both, and Custard's names
   are the better ones.

### 12.14 Where the time goes

`--profile_component FStarC.Custard` prints a breakdown of an extraction.
The counters are Custard's own (`FStarC.Custard.Prof`) rather than
`FStarC.Profiling`'s, for one reason: extraction is a single mutually
recursive traversal, so its counters nest --- `ty_of_typ` calls
`expr_of_term`, which requests a declaration whose body `expr_of_term`
extracts again --- and *inclusive* time attributes everything to the
outermost frame.  `Prof` records **exclusive** time instead: the time in a
counter minus the time in counters called from it, at any depth.  Exclusive
times sum to the whole, which is what makes them comparable.  The guard is
cached, because these sit on functions called a million times and
`Options.profile_enabled` is a namespace-filter match on a string.

The measurement that prompted this: extracting the whole compiler, from
`FStarC.Main.main` plus the 328 entry points, on one core.

| stage | before | after |
|---|---|---|
| SPLIT (the extraction) | 77 s | 48 s |
| ASSEMBLE (file copies) | 0.1 s | 0.1 s |
| MENHIR (grammars + the bytecode pre-pass) | 51 s | --- |
| COMPILE (the OCaml build) | 78 s | 18 s |
| **`make custard`, cache warm** | **3 min 45 s** | **1 min 19 s** |

Peak RSS is 4.4 GB, and the extraction is single-threaded.

Three things were wrong on the extraction side, and all three were
accidentally quadratic rather than anything about the design.

1. **`Loader.loaded` scanned every loaded module.**  It is asked on the path
   from a name to its declaration --- `ensure_lid_available`, which every
   lookup and every call site goes through, about 700k times --- and it
   answered by walking `TcEnv.modules` and lowercasing each of a thousand
   names.  A positive answer is now remembered; only a positive one, since a
   module is never unloaded, and "no" is exactly what the caller is about to
   change.  Worth 27 s, a third of the extraction.

2. **The `Mono` binder-flag queries were recomputed at every call site.**
   `unit_binders`, `type_binders` and `erased_binders` are properties of a
   declaration's *type*, and answering one normalizes every binder's sort;
   they were being asked once per call of the declaration.  `binder_flags`
   caches them per lid, as `binder_classes` already did for §3.1.  Calls into
   the normalizer from `Mono` fall from 634k to 189k, and `must_erase` from
   196k to 60k.  Worth 4 s.

3. **`unit_entries` was quadratic in the program.**  Writing the `.cui` looked
   each declaration's key and type info up by a linear scan of a list as long
   as the program.  Indexing them first takes the `iface` phase from 6.9 s to
   65 ms.

#### The breakdown

With counters down to the level of individual passes, the 48 s the extraction
now takes divides like this.  Everything is exclusive, so the column sums.

| what | time | calls |
|---|---|---|
| `expr_of_term` | 4.4 s | 555k |
| **reading checked files** | **4.2 s** | **808** |
| `specialize` (§3) | 3.6 s | 9.8k |
| `split_mono_args` | 3.6 s | 101k |
| normalization (`norm_bounded_in`) | 3.4 s | 52k |
| `must_erase_for_extraction` | 2.6 s | 578k |
| `Split.run` (§12.9) | 2.5 s | 1 |
| `ty_of_typ` | 2.2 s | 601k |
| reification (`Effects.maybe_reify`, §7.5) | 2.2 s | 9.8k |
| walking the dependency graph for the module roots | 2.2 s | 1 |
| `Simplify`'s `scc` | 1.9 s | 1 |
| printing OCaml (`p.decls`) | 1.4 s | 248 files |
| `string_of_key` | 1.2 s | 970k |
| `Layout`'s rewrite | 0.9 s | 1 |
| `app_of_fv` | 0.9 s | 148k |
| `Rename.run` | 0.8 s | 1 |
| `Simplify`'s `dce` | 0.7 s | 1 |
| `request` itself | 0.7 s | 776k |
| `Simplify`'s `coerce`, `inline` | 0.6 s each | 1 |
| everything else, none over 0.5 s | ~3 s | |

Read as phases rather than as functions: **extraction proper is 32 s**,
**reading checked files 6.4 s**, **the simplification passes 4.7 s**, **the
output side --- `Split`, `Rename`, `Layout` and the printer --- 6.0 s**.

Three things in that are worth saying out loud.

**Reading checked files is 13% and it is not on demand.**  Custard's
demand-driven loader (§4.1) fires exactly *three* times in a whole-compiler
build: batch mode has already loaded everything the entry point's module
depends on.  The 808 loads are the *module* entry points --- the ones listed
for their initializers alone (§4.4), which nothing in the dependency graph
reaches --- and each pulls its own transitive closure through `prime_cache`.
That is unmarshalling, and there is no clever way around wanting those
modules.

**No pass dominates.**  The simplification pipeline is thirteen passes and
the largest, `scc`, is 1.9 s; the printer is 1.4 s for 248 files.  Neither is
where the time is.

**The traversal is the cost, and it is spread over its own machinery.**
`expr_of_term`, `ty_of_typ`, `request` and `string_of_key` together are 8.5 s
over about two million calls, and `must_erase_for_extraction` alone is 578k
calls --- one per node that could be erased.  The two heavier per-definition
steps, `specialize` and reification, are 5.8 s over 9.8k definitions.  That
is a flat profile: no one place left to fix, and the shape one expects of a
traversal that consults the typechecker at every node.

The build stages were the larger target, and both were embarrassingly
parallel work run in sequence on a 256-core machine.  MENHIR's 51 s was a
best-effort `ocamlc -c` of *every* module, done only to have the `.cmi`s the
grammar headers open.  COMPILE's 78 s was one `ocamlopt` over 221 modules in
`ocamldep -sort` order.

Both are gone: the hand-rolled pipeline is now a generated dune project
(§12.11), which does the menhir `--infer` pre-pass properly instead of by
brute force and compiles in parallel.  129 s of the two became 18 s, and the
whole `make custard` 3 min 3 s became 1 min 19 s --- of which 48 s is the
extraction, now much the largest stage again.

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

The corollary is a rule for whoever builds the plugin: *every* module of it
that carries `[@@plugin]` has to be named, not just the one that names the
others.  Getting this wrong produces no diagnostic at build time.  The plugin
links, loads, and then a tactic that should have had a native implementation
falls back to reduction and gets stuck --- `Tactic got stuck!  Reduction
stopped at: reify (Pulse.Lib.Tactics.non_info_tac ())`, reported from wherever
that tactic happened to be used, and in Pulse's case from inside a discarded
`issues` list, so not reported at all.  Pulse's own ML-extraction build already
encodes the rule (`pulse/mk/checker.mk` has a `ROOTS +=` line commented "List
files with plugins here"); a Custard build has to mirror it.
`tests/custard/plugin/CustardPluginAux.fst` is the regression: a `[@@plugin]`
in a module nothing refers to, which registers only because it is a second
`--custard_entry`.

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

#### A polymorphic plugin

A plugin may be polymorphic in a type.  Nothing can be *done* to a value whose
type is unknown, so the embedding for such a type variable is the identity on
the syntax the caller passed --- `mk_any_emb`, which both the syntax and the
NBE embedding libraries provide, and which needs the type argument only to
print it under `--__debug_embedding`.

The type arguments themselves are the awkward part.  The normalizer does not
know that an argument was a type, so it hands the primitive step *all* of
them, while `interp_term`'s combinator (`arrow_as_prim_step_n`,
`mk_tactic_interpretation_n`) is built for the value arguments alone.  So a
match wraps the lambda that `interp_term` already builds, peeling one argument
off the front of the list per type binder and binding it to the variable its
`mk_any_emb` reads:

```ocaml
register_plugin "CustardPlugin.pswap" 4
  (fun psc cb us args -> match args with
   | (tv0, _) :: (tv1, _) :: rest ->
     arrow_as_prim_step_2 (mk_any_emb tv0) (mk_any_emb tv1)
       (e_tuple2 (mk_any_emb tv1) (mk_any_emb tv0))
       custardPlugin_pswap (lid_of_str "CustardPlugin.pswap") cb us rest
   | _ -> failwith "...")
```

Two consequences of the type arguments being ordinary arguments.  The
*registered* arity counts them --- 4 above, for two type binders and two value
binders --- while the combinator's index does not; and the failure branch is a
`failwith`, not a `None`, because a plugin applied to fewer arguments than its
arity is a bug in the normalizer, not a step that declines to fire.

Only *leading* type binders are peeled.  One after a value binder would have to
come out of the middle of the list, and no caller needs that; it is left in
place, where it has no embedding and the plugin is rejected as before.

Nothing the compiler itself builds needs this: of the 163 `[@@plugin]`
declarations in `ulib` and `src`, none is polymorphic.  **Pulse's is.**
`Pulse.Main.check_pulse_after_desugar (decl:'a)` hands its `'a` straight to
`RU.unembed_pulse_decl`, so the type variable never needs a real embedding ---
exactly what `mk_any_emb` is for --- and it registers at arity 4 (one type
argument, two value arguments, and the tactic's own).  `tests/custard/plugin`
covers the four shapes that differ: one type binder used at the argument and
at the result (`pid`), two of them (`psnd`), a type binder mixed with a
concrete argument (`pcount`), and a type variable *under* a real embedding
(`pswap`, whose result is `e_tuple2` of two identity embeddings).

#### An import had no type

Specializing `mk_any_emb` into a plugin is what first dereferenced an
*imported* reference cell: its body reads `!Options.debug_embedding`, and
`FStarC.Options` lives in the compiler unit the plugin links against.  It
printed as `(FStarC_Options.debug_embedding).(0)`, an array index, which does
not compile.

`Extract.import` (§12.4) recorded a linked declaration in `st.names`, so
references resolved to the right name, but not in `st.emitted`, which is where
`callee_sig` and `callee_eff` look.  Every cross-unit call was therefore typed
`TAny` and classified `E_Pure`.  The type is why the dereference printed
wrongly --- the OCaml backend prints `!x` when the operand's type is `TRef` and
an index otherwise --- and the effect is worse: a call to an imported effectful
function could have been dropped or reordered.  Imports now go into
`st.emitted` under the same key an ordinary translation would use.  They do
*not* join `st.order`, which is what the emitted program is read off, so
nothing new is printed.


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
  `pack_fv [...]` that rebuilds it, and otherwise raise error 370,
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

## 14. Migrating an example: DICE

`pulse/share/pulse/examples/dice` is a DICE Protection Environment: about
forty Pulse and F\* modules over a hash table of sessions, calling into
EverCrypt for hashing and signing.  It is the largest Pulse program outside
the compiler, it was already extracted to C through karamel, and every C
feature it uses -- a mutex, a global, a struct-valued hash table, a function
pointer, hand-written C on the other side of an interface -- is one that a
whole-program compiler has to get right.  Migrating it was therefore worth
more as a test of Custard than as a saving for the example.

Both C paths work: Custard emits a `.krml` file that karamel turns into
1535 lines of C, or emits 968 lines of C itself.  Each compiles with
`-Wall -Wextra -Werror`, and the direct output includes four C standard
headers and six lines of the example's own, and nothing else.
`custard.Makefile` alongside the existing `c.Makefile` builds either.

The comparison with `c.Makefile` is the point.  That file passes karamel a
`-bundle` for `HACL`, a second one for `DPE`, a `-library` naming three
modules, two `-add-include`s, and a `--extract` filter listing seven
namespaces to keep and six to drop.  Custard's invocation names the six entry
points and nothing else: there is one translation unit, so there is nothing to
bundle, and the reachable set is computed rather than described.

What the migration cost was eleven fixes to Custard and *no change to the
example's F\* sources*.  None of the eleven is specific to DICE.

### 14.1 A binder query must unfold abbreviations

`EverCrypt.HMAC.compute` is `a:hash_alg -> compute_st a`, and `compute_st` is
an `inline_for_extraction noextract` abbreviation hiding nine further binders,
four of them erased.  `U.arrow_formals_comp` flattens total arrows and
descends into refinements but never delta-unfolds, so every Custard query that
reads "the binders of this declaration" off its *type* stopped at the first
abbreviation and saw a one-binder function.  The surplus spine entries were
left alone, so the caller passed its erased binders at run time and the
karamel backend reported `unbound variable pkey`.

`Extract.peel_typ` already solved this for *result* types, by peeling on the
term and unfolding at each step; `Mono.arrow_formals_unfold` is the same idea
for the binder side, and `Mono.unit_binders`, `Mono.type_binders` and
`Mono.classify` now use it.  Both have to be fuelled, because one unfolding
can expose another -- Pulse's `cont_elab` is the documented case.

### 14.2 `extract_as` on a `val`

`Pulse.Lib.Core.as_atomic` came out as an unresolved external.  It is a `val`
carrying an `[@@extract_as]` attribute, and `fixup_extract_as` -- like the ML
pipeline's `fixup_sigelt_extract_as` -- only handled `Sig_let`.  The ML
pipeline can afford that, because `--cmi` always loads the `.fst`; Custard
meets declarations whose `.fst` was never installed, and `Pulse.Lib.Core` is
one (only its `.fsti` ships).

`fixup_extract_as` now synthesizes the `Sig_let` from a `Sig_declare_typ` plus
its `extract_as` implementation, and marks it `Inline_for_extraction`.  The
marking matters: every `extract_as` in the tree is a small identity or
constant wrapper, and krml rejects `let tmp = r[0] <- x in as_atomic tmp`
because an assignment has to be in statement position.  Inlining the wrapper
removes the binding along with it.

### 14.3 A declaration's result type may not out-run its body

`n_extra` -- how many arrows of the result type the definition's own lambdas
consume -- counted only the binders that *survive* erasure.  An erased binder
still had an arrow in the source type, so a definition written through an
abbreviation over an erased binder came out claiming a larger arity than its
body has:

```ocaml
let eraseAbbrev_add3 (x : Prims.int) (eta : Prims.int) : (Prims.int -> Prims.int) =
  (Prims.op_Addition x eta)
```

which `ocamlopt` rejects.  It now counts every binder past the specialization
spine.  `tests/custard/EraseAbbrev.fst` is the regression test, and it was
written for §14.1 -- it caught this on the way.

### 14.4 Eta expansion, bounded by the callee's arity

krml refuses a partial application at a call site (`Cannot enforce arity at
call-site for Pulse.Lib.Reference.replace`), and emitted
`(HACL_hacl_hash(alg), (void*)0U)(...)`.  `Simplify.eta_expand_decls` gives a
definition whose body is a partial application the arguments it is missing.

The bound is the *callee's* real arity, not the number of arrows in the
caller's result type.  `dl_ret` can legitimately carry more arrows than the
body has room for -- `eta_reduce` moves one there, and §7.3's abbreviation
peeling can leave another -- so expanding by "however many arrows `dl_ret`
has" over-applies, which is how the pass first shipped and how it produced
`Prims.op_Addition x eta eta1`.  Only a body that is `EQual` or an `EApp` of
one, and that passes `cheap_expr`, may be expanded: a body that *computes*
before returning a function must not be re-run per call, which is the
`Cfg.cached_steps` hazard of §13.5 again.

### 14.5 External types

Two types in the example have no F\* definition and must not get a C one
either.  `Spec.Hash.Definitions.hash_alg` is EverCrypt's algorithm tag.
`FStar.Bytes.bytes` arrives through `external/l0/L0Core.fsti`, an interface
with no implementation -- the L0 code is C -- four of whose record fields have
that type; the DICE program passes those records to `L0Core_l0` and never
builds or reads a `bytes` itself.

An abstract `val t : Type0` was previously a `DType` with a `TAbstract` body,
which `PrintKrml` turned into a `DTypeAbstractStruct` and `PrintC` rejected
outright (error 368).  Either way the C output redeclared a type its headers
already define.

The facility is the value one, extended to types.  `[@@custard_extern "Name"]`
and `[@@custard_c_header "h.h"]` on an abstract type declaration produce a
`DType` carrying the new `Extern (target, header)` flag.  `PrintKrml` emits no
declaration for it and spells its uses with the target name; `PrintC` emits no
typedef, includes the header, and stops rejecting it.  The type is also
`NoNewtype`, for the same reason `Rule_opaque` is: its representation is fixed
outside F\*.

An attribute needs a declaration one can edit, and neither of these is:
`FStar.Bytes` is ulib, `Spec.Hash.Definitions` is a vendored copy of a HACL
file, and the whole point of migrating an example is that the example does not
change.  `--custard_extern_type Lid[=name][@header]` says the same thing from
the command line, which is also where it belongs: *which* struct
`FStar_Bytes_bytes` is, is a fact about the program being linked, not about
F\*.  A built-in table with one library's answer in it would be wrong for
every other program, so `Builtins.extern_types` is deliberately empty and the
option is the only source.

Where the declaration lives matters for the same reason.  The first version of
this pointed the direct backend at krmllib's `compat.h`, which is where
karamel declares `FStar_Bytes_bytes` -- a porting aid, a struct of a `uint32_t`
and a `const char *`.  But Custard is meant to *replace* karamel, and C it
emits that only compiles against karamel's headers has not replaced anything.
The example now declares both types in six lines of its own
(`external/c/dice/dice_externs.h`), and the direct backend's output includes
`<stdint.h>`, three other C standard headers, and that file -- and nothing
else.  The krml path needs no header at all, since krmllib and
`EverCrypt_Base.h` are already on that side.

This is Custard's answer to karamel's `-library M`, which does not help here:
`-library` works per bundle or per file, and a whole-program compiler has one
file.

`tests/custard/CExtern.fst` pins both spellings, an external type used as a
record field, and section 14.6's globals, against a header of `static inline`
stubs.

### 14.6 Globals in the direct-to-C backend

`DPE.gst` is a mutex-protected session table, initialized by a computation.  C
requires a constant initializer, so `PrintC` used to reject a parameterless
definition by name.  It now declares the variable uninitialized and assigns it
in `custard_init_globals`, which the generated `main` calls first and which a
program embedding the translation unit has to call itself.  This is what
karamel's `krmlinit_globals` does, for the same reason.  The order is
declaration order, which the SCC pass has already made a topological one.  A
program with no globals gets no `custard_init_globals` at all, and no call to
it; see section 14.11 for how that omission came to be noticed.  Section 17.1
narrows this to the globals that actually need it.

### 14.7 A let-bound lambda that is only called

Pulse's `with_invariants` compiles to a thunk bound to a name and applied to
`()` two lines later, twice over.  krml's own optimizer inlines that; the
direct-to-C backend has no closures at all and rejected it.  `Simplify.reduce`
now substitutes a let-bound lambda into its use when the use is a call and
there is at most one of them.

It does this **only on the direct-to-C backend**, which is the interesting
part.  Beta gives the result the type of the application node it replaces, and
that is not always as precise as the body's own; on the OCaml path a
`ref bool` became `any`, and the OCaml backend prints an `any` reference as an
array, so `used_marker := true` came out as `used_marker.(0) <- true` and the
Custard-built compiler did not compile.  A closure is a legal value on the
other two backends, so there the inlining buys nothing and is not worth that.

> A transformation that only one backend needs belongs behind a test on the
> backend, not in the shared pipeline.

### 14.8 Two clones of one type

With `--custard_monomorphize_types`, `option sid_t` and `option U16.t` asked
for two different clones -- two C structs with identical fields and no
conversion between them -- because `sid_t` is `type sid_t : eqtype = U16.t`
and `Monomorphize.mono_cty` matched on the *unfolded* type but returned the
one it was given whenever the unfolding was not itself a `TApp`.  It now
returns the unfolded form.  `unfold_cty` also stops unfolding an abbreviation
applied to fewer arguments than it has parameters, where the body would keep
the missing ones as free variables.

### 14.9 A match with one arm left

Dead-branch pruning can leave `match sid < ctr with | true -> ...`, which krml
renders as `sid < ctr == true` -- noise, and a `-Wparentheses` warning.

The first fix turned it into an `EIf` whose dead side was a fresh `EAbort`,
which is worse than the disease: it invents a branch the program does not have
so as to fit a shape.  The match was exhaustive before pruning, so if every
other arm is unreachable then this one is taken unconditionally, and the right
answer is that there is no test at all.  `prune` now collapses a single
surviving branch to its body, keeping the scrutinee only when evaluating it is
observable (`take`, as the all-arms-abort case already did) and binding it when
the pattern is a variable the body uses.  A constructor pattern that binds is
left alone, since `depat` turns exactly that into projections.

> Pruning a branch is deleting a test.  A pass that deletes the last test
> should delete the `match`, not rebuild it around something invented.

The DICE output lost fifty lines to this.

### 14.10 What C says about a unit

The direct backend emitted `EverCrypt_AutoConfig2_init(((custard_unit)0))`
against a prototype of its own making, `extern custard_unit
EverCrypt_AutoConfig2_init(custard_unit)`.  It compiles, and it is wrong: the
function on the other side is `void EverCrypt_AutoConfig2_init(void)`, and a
declaration that does not match the definition it is linked against is a bug
that a compiler cannot see.  karamel gets this right, so the same F\* program
through the two C paths disagreed.

`PrintC` already dropped unit parameters from Custard's *own* functions, using
a per-declaration table of which binders survive, and already printed a
unit-returning definition as `void`.  Both now apply to `DExternal` as well.
For a definition the parameter is dropped only when it is unused, because the
body may still need to be a thunk; for an external there is no body, and no
question to ask -- C has no unit value, so whatever the target was declared as,
it was not declared to take one.  An argument list that empties out is spelled
`(void)` rather than `()`, which in C means "unspecified" and would hide the
next arity mismatch.

### 14.11 Blocks that say nothing

The C had runs of `else if (s.tag == DPE_INUSE) {\n}`.  They come from a
unit-valued match most of whose arms return `()`, which is what Pulse code
looks like -- one case of a session state does something and the rest do not.
`EIf` had removed an empty arm since the backend was written; `emit_match`
had not.

Two things make it less free than it looks, and both are about the *last*
arm.  Trimming is sound only at the end of the chain: dropping an empty
`else if (c) {}` from the middle would let the inputs that satisfied `c` fall
through to a later arm.  And `emit_match` emits the last arm *without its
test*, on the grounds that F\* has checked the match is exhaustive so nothing
else can run -- which stops being true the moment an arm is trimmed, since the
do-nothing cases now fall off the end instead.  So a trimmed match keeps every
test and has no `else` tail.

Whether a body emits anything is easiest to answer by emitting it, but a trial
emission has to leave nothing behind: `fresh` and the name allocator are
counters, and letting them run renumbered the variables of the branch that was
*kept* (`ns` came out as `ns_3`).  `scope` was already saved and restored;
`ctr` and `declared` now are too.

Thirty lines of the DICE output went, and the test the fix suggested found one
more, in the previous section's own work: `custard_init_globals` was emitted
even for a program with no globals, an empty function that `main` then called.
It is now emitted only when there is something to initialize.

`tests/custard`'s C rule rejects an empty block anywhere in the output, for
every C test rather than by name -- an invariant is cheaper to keep than a
list of the shapes that have violated it -- and `CExtern.fst` has a
three-armed unit-valued match to give it something to catch.

### 14.12 What is still hand-written

The example's `Pulse_Lib_SpinLock.c` is not copied into the Custard build:
`c.Makefile` passes `-library Pulse.Lib.SpinLock`, but Custard compiles
`Pulse.Lib.SpinLock` from its Pulse source like anything else, and copying the
hand-written file as well is a duplicate definition.  `EverCrypt_Base.h` and
the EverCrypt objects are still external, as they are in the baseline: they
are C, not F\*.

## 15. Migrating a test suite: pulse/test

`pulse/test` is Pulse's extraction regression suite: fifty-eight `.fst` files
that are checked, and twenty of them that are also extracted and compared
against a checked-in `.expected` file --- fourteen to C and six to OCaml.  It
is a different kind of exercise from the DICE example of §14.  DICE is one
program with six entry points and a build of its own; `pulse/test` is twenty
unrelated programs with *no* entry points at all, each one a handful of `fn`s
written to exercise one feature of the extractor, and each one built by the
same three lines of a shared makefile.  What it tests is not that the output
runs but that the output does not change without someone noticing.

The whole suite now goes through Custard.  The `.expected` files were
regenerated, which the exercise was authorized to do: they record one correct
output, not the only one.

### 15.1 Rooting a module

A test module has no `main`.  It has three or four `fn`s that the makefile
extracted by naming the *module*, which is what `--extract_module` means to
the other backends, and what a whole-program compiler has no notion of: a
root is a definition, and a definition is reachable or it is not.

Listing the definitions in the makefile was the obvious repair and the wrong
one.  A test that gains an `fn` would silently stop extracting it, and an
expected-output test that quietly covers less than it says is worse than no
test.  So Custard gained `--custard_entry_module M`, which roots every
top-level `let` of `M`:

```
--custard_entry_module Break --custard_entry_module Goto
```

It roots *values* only.  A type is rooted by the definitions that use it, and
under `--custard_monomorphize_types` a parametric type has no single instance
to root in the first place.  It skips `NoExtract`, projectors and
discriminators, and it skips a definition that is erased --- ghost, or a
result type `must_erase_for_extraction` rejects --- because a Pulse module
states its invariants next to the code that maintains them, and `Null.live
#a (r : ref a) : slprop` is a specification that came out as `let null_live
(r : 'a ref) : unit = ()`.

And unlike `--custard_entry`, it is *quiet*: naming a definition that
extracts to nothing is a mistake worth reporting, and naming a module is
not, because a module normally holds proofs alongside its code.

### 15.2 What still goes through karamel

Four of the fourteen C tests --- `ANF`, `Null`, and both of
`bug-reports` --- have a definition over `Prims.int`.  karamel represents
an unbounded integer as `krml_checked_int_t`, a 64-bit integer with an
overflow check, which is a deliberate affordance for exactly this: test code
that is about something else.  Custard's direct backend has no
representation for an unbounded integer and says so (error 368).

So the harness has two C rules.  `CUSTARD_KRML_C` lists the modules that go
through `--codegen krml` and karamel; everything else is `--codegen c`.  The
list is two names long in `pulse/test` and two in `pulse/test/bug-reports`,
and every one of them is there for `Prims.int`.

### 15.3 The harness

`pulse/mk/custard-test.mk` is included *after* `mk/test.mk` and replaces its
`.ml`, `.krml` and `.c` rules; checking, diffing and recursion are untouched,
so `make accept`, `make ACCEPT=1` and the `.output.expected` tests all still
work.  A later pattern rule with the same pattern overrides an earlier one,
which is how `tests/custard/Makefile` is already structured.

Two make details are worth writing down.  The dotted module name cannot be
recovered from an underscored file name by text substitution, so the `.ml`
and `.krml` rules read it off `$<` (whose prerequisites `.depend` supplies)
and the `.c` rules are generated by a `foreach`/`eval` loop over
`$(wildcard *.fst)`, because `.depend` knows nothing about a target Custard
invented.  And `CUSTARD_CFLAGS := <base> $(CUSTARD_CFLAGS)` rather than
`?=`, so that a `+=` in the client makefile before the include survives.

Every direct-C output is checked by the empty-block invariant of §14.11,
which is how the first of the fixes below was found.

### 15.4 Five fixes

None of the twenty test modules needed a source change.  Five compiler bugs
did come out, three of them about the karamel path, which the DICE example
had exercised much less:

1. **karamel already declares `Prims`.**  karamel prepends its own `Prims`
   file (`Krml.Builtin.prepare`) with the arithmetic on `Prims.int` in it, so
   the `DExternal` Custard emitted for `Prims.op_Addition` was a duplicate
   karamel rejected outright.  `PrintKrml.karamel_declares` names the
   fourteen, and Custard drops its own; karamel's translation of the *uses*
   refers to karamel's anyway.

2. **`BufIsNull` was mistyped.**  karamel has no `is_null`, so Custard
   compares against a null of the same type.  Pointer equality is the
   *polymorphic* one and karamel types it only through an explicit type
   application; left as a bare `EOp (Eq, Bool)` the checker read the width as
   the operand type and dropped the whole declaration.  `Null_test`
   disappeared from `Null.c` this way, with only a `Warning 4` to say so ---
   karamel drops a declaration that fails its Low\* re-check rather than
   failing, so a migration has to diff the declaration list and not just look
   for errors.

3. **`-bundle X=*` is not a rename.**  `X` has to name a module that exists,
   and a whole-program krml file holds exactly one, named `Custard`.  The
   rule builds in a per-test temporary directory with `-no-prefix Custard`
   and copies `Custard.c` out under the test's name.

4. **An `if` with two empty arms.**  The `EIf` case of `PrintC` already
   dropped an empty *else*, and negated the condition to drop an empty
   *then*, but printed `if (c) { }` when both were empty --- which is what
   Pulse's encoding of `return` leaves behind.  It now prints nothing.  This
   is §14.11's invariant catching its second bug.

5. **`null` on the OCaml backend was a `failwith`.**  ML extraction used
   Pulse's own realization: a sentinel `ref` allocated once and compared with
   `==`.  Custard cannot, because under `--custard_split` a per-file sentinel
   is not one value.  So null is the immediate `0` and `is_null b` is `not
   (Obj.is_block (Obj.repr b))` --- an OCaml `ref` is always a block, so the
   test is exact, and it is stateless.

### 15.5 The output

The C is smaller than karamel's and structurally the same.
`Example_Hashtable.c` is 234 lines against 454, with its function pointers
and tagged unions intact; `Break.c` is 75 against 102, because Custard does
not duplicate the loop condition; `Example_Slice.c` is a self-contained unit
over four C standard headers.  The OCaml is close to ML extraction's modulo
Custard's naming and its flatter `let` chains (§6).

Two things are noted rather than fixed.  `InlineArrayLen` produces a VLA,
`int32_t _cbuf1[__anf0]`, which C11 makes optional and C++ forbids; it
compiles under `-std=c11 -Wall -Wextra -Werror` today.  And
`Example_Unreachable.ml` is now a one-armed `match x with | Some b -> b`,
which is partial, but the C output projects unconditionally too, so the two
backends agree and the arm Pulse proved unreachable is absent from both.



## 16. The cross-backend matrix: tests/extraction/backends

`tests/extraction/backends` is a matrix of self-contained modules, each
exposing `main : unit -> Int32.t` that returns `0l` when every check in it
passed and otherwise the tag of the first check that failed.  Every module is
extracted, compiled and *run* on every backend, and the runtime answer is
compared against what F* proved statically.  It arrived on master with three
columns, for ML extraction and karamel's two backends; Custard adds four.

### 16.1 The four columns

Custard has three backends and its Krml one feeds both of karamel's, so:

| id | pipeline |
| --- | --- |
| `custard-ocaml` | `--custard_backend OCaml` then `ocamlfind ocamlopt` |
| `custard-c` | `--custard_backend C` then `cc` -- no karamel at all |
| `custard-krml-c` | `--custard_backend KrmlC` then `krml`, then `cc` |
| `custard-krml-rust` | `--custard_backend KrmlRust` then `krml -backend rust` |

The `.ml`, `.c` and `.krml` intermediates are produced once each and shared,
so the two karamel columns run off one `.krml`.

`main : unit -> Int32.t` is exactly the shape `--custard_main` wants (§4.4),
so three of the four columns need no driver: Custard emits the `int main` and
makes the F* result the process exit status.  The exception is
`custard-krml-c`, where the name `main` belongs to karamel's module rather
than to the F* one, so the rule generates a two-line driver.

### 16.2 Four bugs in Custard

Running twenty-five modules on four columns turned up four defects, three of
them in code generation.

**The OCaml entry point discarded the exit status.**  `entry_calls` in
`PrintOCaml` emitted `let _ = m_main ()`, so a program that returned `50l`
exited `0`.  §4.4 already said the result becomes the exit status and
`PrintC` already did it; the OCaml backend now emits
`let _ = Stdlib.exit (Z.to_int (FStar_Int32.v (...)))` when the entry point
returns a machine integer.

**Integer literals had no width suffix.**  Custard wrote
`((uint64_t)18446744073709551615)`, which does not compile: C gives a decimal
literal the first *signed* type it fits in (C99 6.4.4.1), and that one fits
none, so the cast has nothing to convert.  The suffix belongs on the literal,
not on the cast.  `PrintC` now emits `U` below 64 bits unsigned, `ULL` at 64
and `size_t`, `LL` for signed 64, and nothing for signed below -- with the
one special case that `-9223372036854775808LL` is not a literal at all but
unary minus applied to a magnitude one past `LLONG_MAX`, so it is written the
way `<stdint.h>` writes `INT64_MIN`.  This one fix took the direct C column
from eight compile failures to one.

**Narrow modular operators were not truncated.**  C promotes anything
narrower than `int` before operating, so `~(uint8_t)0` evaluates to `-1`, not
to `255`.  `PrintC.truncate` now casts the result back at `Int8` and `Int16`
width, and only for the operators whose F* meaning is modular: `Not` at a
width, `BNot`, `BShiftL`, and the wrapping `AddW`/`SubW`/`MultW`.  `add`,
`sub` and `mul` carry no-overflow preconditions, and `/`, `%`, `&`, `|`, `^`
cannot leave the range, so none of them needs it.

**Nested casts were fused unconditionally.**  This one is severity 2.  The
`ECast` case of `Layout.rw_expr` collapsed `ECast (ECast (e, _), c)` to
`ECast (e, c)`.  That is sound for a representation coercion -- `magic (magic
x)` is `magic x` -- and wrong for a machine-width conversion, where each cast
is a computation: `uint8_to_uint32 (uint32_to_uint8 x)` came out as bare `x`,
silently keeping the bits F* had asked to lose.  It was wrong on *every*
Custard backend and had gone unnoticed because nothing else round-trips a
value through a narrower type.  Fusion is now refused when both types are
`TInt`.

### 16.3 One bug still open: the machine-integer modules

`ExtIntNe`, `ExtIntShiftArith` and `ExtUIntRotate` are XFAIL on the columns
recorded in the Makefile, for a reason worth stating here because the fix
belongs in Custard rather than in this test directory.

`Builtins.realized_modules` lists `FStar.UInt8` but not `FStar.UInt16/32/64`
or any of the four signed modules.  For those seven, the operations Custard
recognizes are the ones with a primitive rule -- arithmetic, comparison, the
bitwise trio, the shifts, `v`, `uint_to_t`, and the `FStar.Int.Cast`
conversions.  `ne`, `lognot`, `shift_arithmetic_right`, the rotates and the
masks have none, so they fall through and Custard compiles what F* actually
defines them to be: a fold over a `bool` bit vector in `Prims.int`.  That
does not typecheck on the OCaml backend and reaches error 368 on the C ones.
The realizations do define every one of these operations, which is why the
plain `ocaml` column passes what `custard-ocaml` fails.  The fix is to add
the seven modules to `realized_modules` or to give the missing operations
primitive rules; it is written up as finding #18.

### 16.4 NO_ versus XFAIL_, and why Custard needed its own rule

The directory distinguishes a cell that *makes no sense* on a backend
(`NO_`, not built) from one that is *known broken* (`XFAIL_`, built and
required to fail, so that a fix cannot go unrecorded).  The existing
`xfail_rule` takes the F* step as a prerequisite on purpose: for the original
three columns every XFAILed bug is on the backend side, so extraction must
still succeed, and a missing tool or a harness typo cannot masquerade as the
expected failure.

Custard breaks that assumption, because Custard *is* the extractor: finding
#18 stops the pipeline at `fstar.exe`.  A `custard_xfail_rule` was added
whose prerequisite is only the `.checked` file, so an extraction failure can
be XFAILed while a verification failure still cannot.  This matters for
honesty rather than for coverage: error 368 on `ExtIntShiftArith` is a
correct diagnosis about the program Custard was handed and a wrong one about
the program that was written, so the cell records a defect, not a boundary.
Error 368 on `ExtPrimsIntBignum` or `ExtBoolHigherOrder` really is a
boundary, and those stay `NO_CUSTARD_C`.

### 16.5 Where Custard wins

Custard passes five cells the older pipeline XFAILs.  It compiles projectors
itself, so `ExtProjectorOfCtor` never reaches the karamel code that crashes
on a projector applied to a constructor application (#11).  It does not route
`FStar.UInt8` through krmllib, so `ExtUInt8Lognot` is right on the direct C
backend where the ML column is wrong (#3).  And its Krml output avoids three
shapes karamel's Rust backend cannot handle: the missing `lowstar` module
(#10), `ExtUInt128` (#14) and `ExtUIntMask` (#17).  It loses only through
finding #18.



## 17. Two things about the C output

### 17.1 Globals that C can initialize

Section 14.6 gave every parameterless definition the same treatment: declare
the variable uninitialized, assign it in `custard_init_globals`, have `main`
call that first.  That is what karamel does, and for `DPE.gst` -- a
mutex-protected session table built by a computation -- there is no
alternative.

Most globals are not that.  `ExtIntSigned` has twenty-three, every one of them
a literal or a width conversion of one, and all twenty-three were being written
at startup by a function fifty lines long.  A global written that way is not
just slower to start: it cannot be `const`, it occupies `.bss` and is dirtied
on first touch rather than living in `.data` or `.rodata`, and it is invisible
to the constant folding the C compiler would otherwise do at its uses.

`PrintC.static_init` now recognizes the initializers C accepts where the
variable is declared, and those globals are emitted as `int32_t m7 =
((int32_t)-7);`.  For `ExtIntSigned` that removes `custard_init_globals`
entirely, and with it the call from `main`.  A module that has both kinds keeps
the function for the ones that need it: `tests/custard/CExtern` pins exactly
that, a record-valued and an external-valued global in the initializer
alongside two that are not.

The recognized subset is deliberately narrow -- a constant, and a cast or
coercion of one, plus the null pointer -- for two different reasons.  C's own
notion of a constant expression is wider (arithmetic on literals is one), but
nothing is lost by leaving that out, because a global whose initializer is
`2 + 2` has already been folded to `4` by the time `PrintC` sees it.  Struct
and array initializers are left out for a sharper reason: what Custard emits
for a record is a *compound literal*, and a compound literal is not a constant
expression at file scope however constant its contents, so admitting one would
turn a working program into a compile error.

### 17.2 `ECast` against `ECoerce`

The IR used to have one node for two unrelated things.  `ECast (e, t)` was
both the representation coercion of section 5.4 -- `Obj.magic`,
`Ghost.reveal`/`hide`, the `TAny` boundaries `coerce_prog` inserts -- and the
machine-integer conversion of section 8.1, `FStar.Int.Cast.uint32_to_uint8` and
friends.  They look alike in C, where both are a cast, and nowhere else.

The difference that matters is that a coercion *computes nothing* and a
conversion does.  Section 5.4's rule 2 fuses nested coercions, which is sound
because `magic (magic x)` is `magic x`; applied to a conversion it deletes the
narrowing that was the whole point, and `uint8_to_uint32 (uint32_to_uint8 x)`
becomes bare `x` -- a severity-2 miscompilation on every backend, which is
exactly what section 16.2 found.  The fix at the time was a side condition on
the fusion rule, testing whether both sides were `TInt`.  That works, but it
puts the burden on every pass to re-derive from the types a fact the front end
knew for certain, and to remember to.

So the node is split.  `ECoerce` is section 5.4's; `ECast` is section 8.1's,
and its target is always a `TInt`.  Nothing else changed about either, and the
split pays for itself immediately in three places:

* `Layout.rw_expr` fuses `ECoerce` unconditionally and fuses `ECast` never.
  Neither rule has a side condition, so neither can have the wrong one.
* `Driver.lost_cast`, which decides what `--custard_warn_any` reports, loses
  its `TInt, TInt -> false` clause: a conversion is not lost information, and
  now that is a question of which node this is rather than of what its types
  happen to be.
* `PrintOCaml` had one case analysis doing both jobs, since OCaml needs a real
  call for a conversion and a bare `Obj.magic` for a coercion.  It is now two
  functions, and `index` -- which looks through a cast to keep array subscripts
  readable -- looks through a coercion always and through a conversion only
  when the target width can hold every value of the source.  That was the same
  latent bug in a second place.

`tests/custard/MachineInts` gained the round trip, so the fast suite pins it
too; `tests/extraction/backends/ExtIntCast` pins it end to end on all seven
columns.

### 17.3 Tagged structs, and why a recursive type needs them

C has no way to say "a struct containing itself", and section 8b's `check_finite`
rejects that outright.  What it does *not* reject, correctly, is a struct
reaching itself through a *pointer*: `occurs` stops at a pointer, because a
pointer is a size.  `type tree = ... | Node of node and node = { left: ref tree }`
is therefore accepted, and is ordinary C.

It was not, however, emitted as ordinary C.  Every struct went out as an
anonymous typedef:

```c
typedef struct { CRecType_tree *left; } CRecType_node;
```

and the name `CRecType_tree` does not exist yet -- it cannot, since `tree`
mentions `node`.  Reordering the declarations does not help; that is what
recursion means.  gcc says `unknown type name`, and the whole translation unit
is lost.  Reported against EverParse's `cbor_raw`, where it was the only defect
in the output: adding tags by hand and changing nothing else gave C that
compiles clean under `-std=c11 -Wall -Wextra -Werror`.

So every struct now carries a tag, `t_s` for a type named `t`, and every tag is
forward-declared in one block before any type is defined:

```c
typedef struct CRecType_node_s CRecType_node;
typedef struct CRecType_tree_s CRecType_tree;

struct CRecType_node_s { CRecType_tree *left; ... };
struct CRecType_tree_s { ... };
```

An incomplete type is enough to declare a pointer to it, so the order of the
definitions stops mattering and Custard does not have to compute one.  This
applies to a record, and to a variant that is not an enum -- an enum is not a
struct and needs nothing.  Type abbreviations are unchanged.

`tests/custard/CRecType.fst` covers the three shapes that failed differently:
a variant reaching itself through a record declared after it, mutual recursion
between a record and a variant, and a variant reaching itself directly.  It is
compiled and run, so the pointers are dereferenced and not merely declared.


## 18. A call spine is longer than its head's type

### 18.1 Erased arguments through a variable

`U.arrow_formals_comp` flattens arrows, and an abbreviation is not an arrow
node, so it stops there.  A definition whose codomain is written as an
abbreviation therefore looks like it takes fewer arguments than it does, and
every argument past that point is *unclassified*.  The permissive default --
leave the surplus spine alone -- then passes the erased ones at runtime, to a
callee that deleted the corresponding parameters.  What comes out is a `()`
in a position that no longer exists, and every argument after it shifted by
one.

This is why `Mono.arrow_formals_unfold` exists, and `classify`, `unit_binders`
and `type_binders` have all used it since EverCrypt's `compute` showed the
problem up.  `erased_binders` did not, and it is what filters the spine of a
call whose head is a *variable* rather than a name:

```fstar
let step_t (n:int) = x:int -> g:G.erased int -> y:int -> Tot int
let twice (f : step_t 0) (x:int) : int = f (f x (G.hide 1) 1) (G.hide 2) 2
```

`f`'s sort is `step_t 0`, which has no arrows at all, so nothing was filtered
and `twice` came out as `f (f x () 1) () 2` against a two-parameter `f`.

The fix is `Mono.erased_binders_unfold`, and the reason it is a second
function rather than a change to the first is that the two callers want
different things.  Filtering a definition's own binders, or a type's own
arrows, wants the plain one: the binders in hand came from
`arrow_formals_comp`, and flags that outran them would be aligned against
nothing.  Filtering a *call spine* wants the unfolding one, because the spine
is as long as the call is.

Reported against EverParse's CBOR stack, where the shape is a Pulse `fn rec`:
a recursive `fn` hands its own recursive call to its body as a closure, so the
head is a local whose sort is the `fn`'s type -- an abbreviation.  The symptom
was `Custard: unbound variable pm reached the karamel backend`, `pm` being an
erased `perm` that the definition had correctly dropped and the call site had
not.  `tests/custard/EraseAbbrev` had the name-headed half of this all along
and now has the variable-headed half too, through a binder and through a
`let`.

### 18.2 An arity indexed only by values is a type parameter

`is_type_param` used to hold of a binder of kind `Type` and of nothing else.
The reason is real: neither OCaml nor C has a type variable standing for a
type *constructor*, so the `m` of `class monad (m:Type -> Type)` can be
neither declared nor passed, and uniform compilation makes dropping it sound
because every field whose type mentions `m` is already `any`.

But an arity is not always a type constructor.  `b : header -> Type` takes a
*value*, and values are erased from the target's type language, so `b h` and
`b h'` are the same target type -- there is exactly one of it, and a type
parameter is precisely what names one type.  The distinction that matters is
therefore not "is this `Type`" but "does any argument it takes have kind
`Type`":

```fstar
noeq type payload (h: header) =
  | Small : squash (is_big h == false) -> (v: U8.t) -> payload h
  | Big   : squash (is_big h == true)  -> (v: U8.t) -> payload h

let parse (t: U8.t) : dtuple2 header (fun h -> payload h) = ...
```

`payload`'s own index is dropped correctly -- it is a value index and has no
counterpart in a target type.  What went wrong was `dtuple2`, whose second
parameter is `b : a -> Type`: dropped, `Mkdtuple2`'s second field is typed by
a name that no parameter binds, so it is `any`.  Direct-to-C then rejects the
program outright (error 368) and the krml path emits `._2 = (void
*)IndexedSquash_mk(h)`, which gcc rejects.  Kept, the field is an ordinary
`TVar` and a monomorphizing run fills it in:

```c
struct Prims_dtuple2__header_payload_s {
  uint8_t _1;
  IndexedSquash_payload _2;
};
```

Three pieces, and each is forced by the first:

* `Mono.is_value_indexed_arity`, and `is_type_param` accepting it.
* `ty_of_typ` translating an *application* of such a binder, `b x`, as the
  parameter itself.  The arguments are values, which is what made the binder
  representable, so there is nothing for them to do.
* `ty_of_typ` translating the *argument*, which the source writes as a lambda
  -- `fun h -> payload h`.  Its binders are values and a value cannot reach a
  `cty`, so the body's own translation is the answer; a body that really does
  depend on its index is a `match` or a bare name and falls through to `any`
  on its own, exactly as before.

One thing this breaks and then fixes.  `FStar.Set.set a = restricted_t a (fun
_ -> bool)` was the motivating case for `has_unrepresentable_param`, which
unfolds an abbreviation whose parameter the type language cannot hold.  Now
it *can* hold it, so nothing unfolds, and `set a` is an honest `TApp` of a
two-parameter abbreviation whose body is an arrow.  Section 13.5's result-type
peel looked for a `TArrow` and a `TApp` is not one, so `union` came out with
three parameters and a result type that still had the third arrow in it.  The
peel now goes through `head_ty`, which is the same unfolding every other
consumer of an abbreviation already does.

Reported against EverParse, where the shape is the whole LowParse idiom -- a
parsed header value indexing the type of the payload -- and `Prims.dtuple2@-
initial_byte_t` being `any` took out validate, parse, equal and serialize
alike.  `tests/custard/IndexedSquash.fst` is the reporter's own reduction,
compiled and run through the direct C backend; `tests/custard/Realized` had
`(Prims.int, Obj.t, Obj.t) dtuple3` pinned as expected output and now has
`(Prims.int, bool, string)`.

### 18.3 A budget is only as good as the name it prints

Error 365 says a normalization ran past `--custard_norm_budget`, and the only
thing a reader can do with it is find the definition that provoked it.
`Extract.norm_bounded_in` printed that all along: the extractor holds a
request chain (section 3.6), and the message ends with `Reached through:` and
the keys that led to the term.

`Mono.norm_bounded` did not, and it is the one that matters for the hard
cases.  `Mono` sits below the extractor -- `is_arity_aux` normalizes a
binder's sort, `is_star_aux` a binder's kind, `arrow_formals_unfold` an arrow
spine -- so a budget exhausted in *type-level* work named no definition at
all.  That is what the EverParse report hit on
`LowParse.Pulse.Recursive.validate_recursive_step_count`: the term was
printed and the reader still had to bisect the module to learn what was being
extracted when it appeared.

The fix is a hook rather than a dependency.  `Mono.chain_reporter` is a `ref`
to a `unit -> list document`, defaulting to reporting nothing, which
`Driver` points at `Extract.request_chain` for the one state it builds.
Threading the extractor's state into `Mono` instead would have meant
threading it through every arity test, and the default keeps `Mono` usable
from a plugin or a unit test where there is no extraction in progress.

A synthetic reproduction is worth recording, because the obvious ones do not
work.  A module's *body* normalizations are budgeted too and are almost
always the more expensive, so any ordinary module fails in `Extract` first.
And `Mono`'s step lists have no `Primops`, so a recursive type-level
definition guarded by `if n = 0` stops after two steps rather than unfolding.
What does it is a long chain of abbreviations, each of which is one unfold,
in a definition with no body to speak of:

```fstar
let a0 = Prims.int
let a1 = a0
(* ... 300 of them ... *)
let f (x : a299) : Prims.int = 1
```

extracted with `--custard_entry NBChain3.f --custard_norm_budget 50`.  Before
the hook the message ended at ``The term ... was: a299``; now it ends with
`Reached through: NBChain3.f`.  There is no regression test: `tests/custard`
has no negative-test rule, and adding one for a diagnostic is not worth a
category.

Whole-module extraction of `CBOR.Pulse.API.Det.C` takes 6m20s against seconds
for individual entries, and the reporter profiled it.  The numbers settle the
question and they contradict what this section first claimed:

```
374692 ms  Extract.norm   (509 calls)
   598 ms  Mono.norm    (11631 calls)
   557 ms  cachefile      (287 calls)
```

`Extract.norm` is 374.7s of a 380s run and everything else is noise.  Against
call counts of 329, 374, 393 and 509 for growing root sets -- times 17.7s,
19.1s, 19.0s and 374.7s -- the call count rises by 30% while the time rises
twentyfold, and adding roots is *sub-additive*, which is the specialization
cache doing its job.  So the earlier explanation, that more roots mean more
per-call-site keys and the growth is in the output, is **wrong**: the growth
is in the per-call cost.  A handful of individual normalizations are enormous,
and the recursive-parser step counts are the standing suspicion, since
`LowParse.Pulse.Recursive.jump_recursive_step_count` is what exhausted the
budget in the first place.  Nothing here is super-linear in the number of
roots; whole-module extraction simply reaches a few definitions that
individual entries do not.

That does not change the intended workflow -- one run, one interned
specialization table (section 4.4) -- since splitting gives up the sharing.
It does change what to look at next, which is a bisection down to the
individual definitions whose normalization is expensive, rather than anything
about keys or interning.

The reporter did that bisection, and the answer is two definitions.  His
run breaks down per entry point:

```
cbor_det_validate         545 ms/call
cbor_det_serialize         53 ms/call   (more calls)
```

Five hundred milliseconds against fifty, with the *cheaper* one making more
calls, confirms that this is a handful of enormous reductions and not a count
of them.  Lowering `--custard_norm_budget` until error 365 fires names them:
`LowParse.Pulse.Recursive.validate_recursive_step_count` applied to
`serialize_raw_data_item_param`, reached through
`validate_recursive_step_count_leaf`, `validate_raw_data_item`,
`cbor_validate`, `cbor_validate_det'`, `cbor_validate_det` and
`cbor_det_validate`; and the `cbor_compare` specification inside
`cbor_match_serialized_tagged`'s `fn` type.  Each needs between 3x10^7 and
10^8 steps -- `--custard_norm_budget 30000000` fails on them and `100000000`
succeeds -- which is what a step-count function for a recursive parser costs
when it is unfolded rather than left as a call.

Both are *specification* terms that reach a type Custard has to look at:
the step count indexes the parser's type, and `cbor_compare` appears in a
`fn` type's precondition.  Neither contributes anything to the output.  That
suggests the fix is not to make normalization faster but to stop asking for
these terms at all, which section 5.1 already does for values and does not
yet do for the type-level positions that only exist to be erased.

`--profile FStarC.Custard` reports the phase breakdown when a run does need
to be explained.

## 19. What the retest found

The four fixes of sections 17.3 and 18 were retested against EverParse's CBOR
stack, and the headline is that whole-module extraction of
`CBOR.Pulse.API.Det.C` now runs to completion -- 3419 lines and 333 functions
of direct C, where before it died on `Error 368` in `Prims.dtuple2`.

What follows is three rounds of that loop rather than one, because the first
two fixes were partial and one of them was aimed at the wrong cause.  19.1
and 19.3 were confirmed on the real output; 19.3 earned its keep immediately,
turning three functions that had been silently emitting broken spines into
three honest errors.  19.2 records a diagnosis that the next round disproved,
and 19.4 is what the defect actually was.

### 19.1 A field held by value needs a definition, not a tag

Section 17.3 forward-declares every struct, which is what a field reaching
its own type *through a pointer* needs: an incomplete type is enough to
declare a pointer.  A field held **by value** is not enough, because the
compiler has to know its size to lay out the struct containing it, and the
forward declaration says nothing about size.

Custard receives its declarations in the SCC pass's order, which is computed
over *all* dependencies.  A pointer edge is one of those, so a group made
cyclic through pointers is a single SCC and the order inside it is arbitrary
-- and that is exactly where a by-value field lands ahead of its definition:

```c
typedef struct Pulse_Lib_Slice_slice__cbor_raw_s Pulse_Lib_Slice_slice__cbor_raw;
...
struct CBOR_Pulse_Raw_Type_cbor_array_s {
  uint8_t cbor_array_length_size;
  Pulse_Lib_Slice_slice__cbor_raw cbor_array_ptr;   /* incomplete here */
};
...
struct Pulse_Lib_Slice_slice__cbor_raw_s { ... };   /* only at the end */
```

The by-value edges are necessarily acyclic -- that is precisely what
`check_finite` establishes -- so they always have a topological order, and
`PrintC.sort_types` emits the definitions in one.  It is a depth-first walk
in the original order, so a type with no unmet dependency keeps its place and
the diff against the previous output stays small.  The forward declarations
are unchanged and still absorb every pointer edge, which are the ones that
make the graph cyclic in the first place.

`tests/custard/CByValue.fst`.  Getting it to bite took one attempt more than
expected: a source bundle of mutually recursive types is *already* ordered by
dependency, so no arrangement of `type ... and ...` reproduces it.  The
container has to be **polymorphic** -- `slice raw` is a monomorphized
instance, created when the request for the type that holds it reaches it, and
so emitted after it.  Which is EverParse's shape exactly, `slice` being
`Pulse.Lib.Slice.slice`.

### 19.2 An empty classification is not "everything is Poly"

Section 18.1 fixed a call spine whose head is a *local variable*.  The report
came back with the same symptom on a head that is an **fv**, which that
section explicitly claimed was always right, on the ground that
`Mono.classify` unfolds abbreviations and so always sees the full arity.

The first guess was that `Extract.binder_classes` had lost the declaration:
it looks it up with `TcEnv.lookup_sigelt` and returns `[]` on a miss, and `[]`
is not "every binder is `Poly`" but a short-circuit -- `split_mono_args` sees
no `Mono` and no `Dropped` and hands the whole spine back untouched.  It now
falls back to `lookup_lid_typ`, which is the lookup `binder_flags` has always
used, so that the spine and the flags cannot be computed from different
declarations.

**That guess was wrong, and the instrumented retest said so plainly**: the
sigelt lookup never misses, and the classification comes back *short* rather
than empty -- one entry for a call spine of four.  The real cause is section
19.4, and the fallback survives only because a short-circuit that cannot be
told from an answer is worth closing whatever else is true.  It is recorded
here rather than quietly deleted because the shape of the mistake is the
useful part: an inference from "which code path could produce this symptom"
picked a plausible path and the wrong one, and only a `printf` in the
reporter's own build settled it.

### 19.3 The C backend should not print a name it cannot resolve

The defect in 19.2 is in the IR, and only the karamel backend caught it.  It
catches it by accident of representation: karamel's terms are De Bruijn, so
the translation has to *find* an index, and `PrintKrml.find` fails loudly
when it cannot.  The direct-to-C backend prints names as names, and
`lookup_var` fell back to `c_var x` on a miss -- so the same broken spine
came out silently, and surfaced as seventy gcc diagnostics about the code
*after* it.

`lookup_var` now rejects.  Every binder reaches `bind_var`, `bind_cell` or
`bind_alias` before its scope is printed and `reset_scope` runs per
definition, so a miss is real; top-level names are `EQual` and never come
through it.  The message is `reject_ir` rather than `reject`, a distinction
worth drawing in the output: `reject` says C cannot express this, which is a
fact about the source and something the reader can act on, and `reject_ir`
says the IR is malformed, which is a fact about the compiler and something to
report.

### 19.4 A definition's arity is a fact about its lambda

A real defect, found while looking for 19.2 and **not** the cause of it --
that is 19.7.  It is kept because it is a genuine disagreement between two
sources of truth, it has a reproduction, and the classification it produces
is the one a call site needs whenever the lambda is in scope.

`Mono.classify` reads a definition's binders off its **type**;
`Extract.extract_letbinding` reads them off the definition's own **lambda**,
via `U.abs_formals`.  Those two agree almost always, and when they do not,
the emitted definition and its call sites disagree about how many arguments
there are.

EverParse's `jump_header : unit -> jumper parse_header` looked like the case
and was not: the retest showed `lb.lbdef` is `Tm_unknown` there, since the
declaration comes from an interface and the body is not in scope, so the
extension has nothing to extend with and is a no-op.  What it *does* cover is
every definition whose body is in scope, which is why the reproduction below
is a single file -- and the reproduction is real, so the disagreement is
real.

The tempting fix is to unfold harder, and it is the wrong one.  Whether an
abbreviation can be seen through is a fact about the environment the
normalization happens to run in, and there is always another way to write a
type whose arrows are not syntactically arrows -- the regression test uses a
refinement, `(r:step_t 0{...})`, which is a `Tm_refine` and therefore not a
`Tm_arrow` no matter how much unfolding is allowed.  A type-level `let rec`
does it too, since these step lists deliberately omit `Zeta`.

So the fix is to derive both sides from the same list.  `Mono.classify_def`
is `classify` extended with the binders of the definition's own lambda that
the type's spine stopped short of, classified by `Mono.is_erased_binder` --
which is, verbatim, the rule `extract_letbinding` already applied to exactly
those binders:

```fstar
let flags = bs |> List.mapi (fun i b ->
              nth_class i || (i >= n_poly && Mono.is_erased_binder (tcenv st) b))
```

`binder_classes` calls it with `lb.lbdef` in hand.  Every consumer of a
classification -- `split_mono_args`, `call_unit_flags`, `call_type_args` --
then agrees with the definition without knowing anything was extended, which
is the property that was missing: the two sides were derived from two lists
that usually coincide, and now they are derived from one.

Deliberately `is_erased_binder` and not also `is_unit_binder`: a definition
*keeps* a unit-shaped binder past its classification, so a call site has to
keep passing one.  The extension is a no-op whenever the type's spine is
already as long as the lambda, which is the overwhelmingly common case, so
nothing that worked before can change.

`tests/custard/EraseAbbrev.fst` grows the case, and it was checked to fail
without the fix, with the emitted call reading `add5 () x () 6` against a
three-parameter definition -- the reported symptom exactly, arrived at from
the other end.

### 19.5 A binding nothing reads

A pattern match names the fields of the constructor it matched, and a body is
under no obligation to use any of them.  The match compiler emitted the
binding anyway, so C came out with a declaration, an initializer and no use,
and a build with `-Werror=unused-variable` refused the file over it:

```c
CBOR_Pulse_Raw_Type_cbor_raw _letpattern_8 = x_;
```

`PrintC` now drops an `ELet` whose bound name does not occur in the body,
provided the initializer is `is_pure`.  Purity is the side condition that
matters and it is not negotiable: an initializer that does something still
has to run, and one that does not can go with the name.  `vars_of`
over-approximates the occurrences -- it ignores shadowing -- which is the
safe direction, since the only question asked of it is whether a name is
*definitely* unused.

This lives in the printer rather than in `Simplify` on purpose.  It is a fact
about C, which has no way to say "declared and unused on purpose" that does
not vary by compiler, and not a fact about the IR; OCaml's warnings are off
in the generated header and karamel does its own elimination.

`tests/custard/CDeadLet.fst` covers it, and since these tests compile with
`-Wall -Wextra -Werror`, the file building at all is the assertion.

### 19.7 A normalizer returns a meaning, not a tag

This is what 19.2 actually was, and the reporter found it by instrumenting
`arrow_formals_unfold_aux` in his own build.  The answers to the two
questions that section left open are both "no": `U.is_total_comp` is true,
and the `norm` call does *not* hand `jumper parse_header` back unchanged.  It
unfolds it perfectly, and returns exactly the arrow that was wanted --
wrapped in a `Tm_ascribed`.

`SS.compress` resolves unification variables and delayed substitutions.  It
does not strip an ascription, and an ascription's tag is not `Tm_arrow`, so
the `| Tm_arrow _ ->` case did not fire and the spine stopped one
abbreviation short.  The fix is one line:

```fstar
let r = strip r in
match r.n with
| Tm_arrow _ -> ...
```

His tag census over a single `jump_header` run is the part worth keeping,
because it says this is the common case rather than a corner of it: of the
terms tested for `Tm_arrow`, **six** were arrows behind an ascription and
**twenty-four** more were refinements behind one.

So the generalization is not optional.  F* has two nodes that carry no
meaning -- `Tm_ascribed`, which records a type the elaborator wrote down, and
`Tm_refine`, which records a proposition erased long before any of this --
and *no* shape test in `Mono` now reads a tag without going through
`Mono.strip`, which alternates the two away to a fixed point (an ascription
can hide a refinement and a refinement's base can be ascribed).  `is_arity`
and `is_star` had been peeling refinements only; `Extract.peel_typ` and
`Extract.is_prop_sig` had the same pattern and now use `strip` too.

The failure mode is what makes this worth a section.  Reading the tag off a
wrapper answers "not an arrow" and "not an arity", and both of those are
wrong in the direction that **miscompiles** rather than the direction that
rejects: a short spine silently keeps arguments the callee deleted, and a
missed arity silently turns a type binder into a runtime one.  Nothing about
the shape of a term should ever be concluded from a single node.

With this, whole-module direct-to-C extraction of `CBOR.Pulse.API.Det.C`
succeeds, the 3419 lines compile under `gcc -Wall -Wextra`, and all 57 entry
points of the module extract individually.

### 19.8 A cell that is written and never read

Two `-Werror` blockers, both about C rather than about the IR, and both fixed
in `PrintC`.

The first is 19.5's dead binding, which did not fire on the reported case.
The side condition was `is_pure`, and the `_letpattern` there was bound to a
*collapsed cell*, which `is_pure` rejects -- rightly, since a read of a cell
cannot move across a write to it.  But dropping is not moving.  A read whose
result nothing wants can always go, because reading a cell Pulse has
established is live does nothing observable.  So the predicate is now
`is_droppable`: `is_pure` with reads allowed, and nothing else changed --
a call, a write, an allocation, a loop and an abort are as undeletable as
they are unmovable.  The distinction is worth two functions rather than a
flag, because "may this move" and "may this go" are asked in different places
and the wrong answer to either is a miscompilation.

The second is Pulse's loop measure: `fn while` carries a decreasing value the
checker needs and the program does not, so it arrives as a `let mut` whose
type has erased to `custard_unit` and whose writes assign a constant.  C says
`-Wunused-but-set-variable` and C is right.

`PrintC.cell_dead` is the side condition and it is stricter than "never
read": *every* occurrence of the name must be the cell operand of a write.
That rules out the two ways a cell is used without being read -- an address
taken and passed somewhere, and a read whose value the surrounding term does
something with -- and it makes the licence syntactic rather than an argument
about aliasing.  The written values and indices must be `is_droppable`, since
dropping the write drops them.  `PrintC.drop_writes` then replaces those
writes with the unit they evaluate to, and nothing else in the term mentions
the cell, so the declaration goes too.

The alternative was `(void)x;`, which is what this backend already emits for
an unused *parameter*, where it is the only option -- a parameter cannot be
deleted without changing the signature.  A local can, and a suppression that
keeps a dead variable is worse output than no variable.

### 19.10 A second name is not worth a variable

The `_letpattern` of 19.8 survived, and the reporter dumped the IR rather
than guess at why.  The dead-let rule was right to decline: the name *is*
read, by the match it scrutinizes.

```
let _letpattern : cbor_raw = x' in
match _letpattern with
| CBOR_Case_Tagged(tg) -> res1
```

What happens next is that `emit_match` finds the scrutinee `is_stable`, takes
the direct path and emits no read of it, and binds `tg` with `bind_alias`,
which emits nothing because the body never mentions it.  The declaration is
left with, in the end, no users at all.

So this is not a dead binding, it is a **redundant alias**: `let x = <stable
expr> in e2` declares a second name for a value the backend never assigns to.
The machinery was already there and already used for exactly this reason --
`emit_match`'s direct path, and every pattern binding -- so the fix is to
bind `x` to the path instead of declaring a copy of it.  No side condition
beyond `is_stable`, which is the same licence `emit_match` has always taken:
a variable that is not a collapsed cell, or a projection out of one, is
something this backend never writes to.

It is worth more than the two warnings it closes, because the *live* case
collapses too.  `Pulse_Lib_HashTable` loses four copies of a function
pointer:

```c
- size_t (*hashf)(size_t) = ht.hashf;
- size_t cidx = ..._mod(hashf(k), ht.sz);
+ size_t cidx = ..._mod(ht.hashf(k), ht.sz);
```

and `Example_Slice` loses a pointer copy in a two-line function.  In
EverParse's output `_letpattern` bound to a plain variable appears 335 times.

### 19.11 A specification named as an entry point

`--custard_entry CBOR.Pulse.API.Det.C.cbor_det_match` was rejected with error
367, the recursive datatype `Prims.list`.  Every word of that message is true
and none of it is an answer to what was asked.  `cbor_det_match` is a
separation-logic predicate:

```fstar
val cbor_det_match : perm -> cbor_det_t -> Spec.cbor -> slprop
```

Its result is `slprop`, so it has no runtime content at all; `Spec.cbor` is a
*ghost index*, and nothing in the program holds one.  The layout pass was
asked to lay out a type that exists only in the proof.

The whole-module path already got this right, and had for a while:
`erased_definition` is what keeps `--custard_entry_module` from rooting the
specifications a module keeps alongside its code.  A root named one at a time
was "taken at its word", which is a defensible policy for a name the user
typed and an indefensible one when the word is `slprop`.  So the same
question is now asked of an explicit root, in `Extract.root_is_erased`, before
it is requested rather than after.

Not silently.  A misspelled `--custard_entry` is an error rather than an
empty output, and a correctly spelled one that turns out to name a proof is
the same kind of mistake: the user asked for something and did not get it.

The predicate is *not* `erased_definition`, and finding out why took two
rounds of the test suite.  `must_erase_for_extraction` answers yes for
`unit` -- correct about the value, wrong about the definition, since `main :
unit -> ML unit` returns nothing and is the entire program.  A definition is
contentless only when its result is non-informative *and* computing it does
nothing, so the effect has to be total or ghost.  And a *type* is exempt
outright, for the reason it is a legitimate root at all: its result is
`Type`, than which nothing is less informative, and a type abbreviation named
by `--custard_entry` is exactly what a hand-written realization needs emitted
(section 12.7, and `tests/custard/TypeEntry.fst`, which is what caught this).

`tests/custard/pulse/PulseSpecRoot.fst` covers both halves -- the module path
compiles and mentions no `tree`, the two explicit roots report a
specification -- and is the suite's one negative test, so it has a rule of
its own.

### 19.12 A closed lambda is a function without a name

C has no closures, and the direct backend rejects a lambda for that reason.
That is the right answer only when the lambda *captures* something.  A closed
one is an ordinary function that nobody named, and the address of a top-level
function is a value C stores in a struct and passes as an argument without
complaint.

The reporter isolated it to one pair of files.  A record of function fields
filled in with *names* already worked, and produces exactly the C the karamel
path produces:

```c
struct FunPtrRecord_iter_t_s {
  uint64_t contents;
  bool     (*impl_validate)(uint64_t);
};
...
  return (FunPtrRecord_iter_t){ .contents = x,
                                .impl_validate = FunPtrRecord_is_even };
```

The same record written with the function inline was error 368.  So the whole
of the gap is whether the function had a name, and the whole of the fix is to
give it one.

`Simplify.lift_lambdas` walks each definition, and every `EFun` with no free
term variables becomes a fresh top-level `DLet` named after the definition it
came out of, with an `EQual` in its place.  It runs before `dce`, which reads
the final call graph and would otherwise drop the new declarations as
unreachable, and before `scc`, which orders them.  Free *type* variables are
not an obstacle: the lifted declaration takes the enclosing one's type
parameters and the reference instantiates them, which costs nothing under
`--custard_monomorphize_types` and stays correct without it.

Only for `--custard_backend C`.  OCaml has closures and karamel has its own
treatment, so lifting for either would churn the output to no purpose.

Nobody writes these.  They come from an `inline_for_extraction` record of
thunks -- `val cbor_det_share () : share_t cbor_det_match` -- whose fields
beta-reduce to bare lambdas when the record is built.  Of the forty fields of
EverParse's `CDDL.Pulse.AST.Det.C.cbor_impl`, nineteen are bare names and
already worked, ten are erased ghost fields, and the remaining eleven are
lambdas -- every one of them closed.

The diagnostic changed with it, because it was giving the wrong advice half
the time.  A lambda that reaches `PrintC` now has survived lifting, so it
captures, so it really is a closure; the message says that, and offers naming
the captured values as parameters alongside the `[@@@monomorphize]` route.
`tests/custard/CFunPtr.fst` is the positive test and `CNoClosure.fst`, which
captures, remains the negative one.

### 19.13 Advice that names a flag the reader has already set

`--custard_monomorphize_types true` was set, and the direct backend said:

```
  - Custard: the type variable 't has no C representation, in ...
  - The direct-to-C backend requires --custard_monomorphize_types true.
```

Unactionable, and worse than unactionable: it sends the reader to check their
command line, which is the one place the problem is not.  `PrintC.mono_advice`
asks whether the flag is on.  If it is off, it is still the whole answer.  If
it is on, the monomorphization pass ran and did not reach this type, which is
a Custard bug and is now reported as one.

### 19.14 A refinement is a proposition, and no question here depends on one

`Extract.is_type_sig` decides whether a declaration is a type or a value, by
normalizing its result type and looking for `Type`.  `is_prop_sig` asks the
neighbouring question about `prop`.  Both normalized the result *whole*,
including any refinement on it, and then peeled the refinement off the answer
and threw it away.

For most declarations that is a small waste.  For EverParse's CDDL layer it
is a hard stop:

```
* Error 365:
  - Custard exceeded --custard_norm_budget (1000000000 reduction steps)
    while normalizing a type signature.
  - The term being normalized, before reduction, was: e':
    CDDL.Pulse.AST.Bundle.bundle_env ... { bundle_env_included ... /\
    e'.be_ast == wf_ast_env_extend_typ_with_weak ... }
```

`env9`'s type is a well-formedness condition on a machine-generated CDDL
environment built up one entry at a time, so each successive definition drags
in the whole accumulated chain.  A budget of 10^9 steps is not the problem and
raising it would not have helped; the proposition has no bearing on whether
`env9` is a type.

So both tests strip first.  `Mono.strip` is syntactic, so this moves the peel
from after the normalization to before it and the answer is unchanged by
construction -- `is_type_sig` already looked through `Tm_refine`, and
`is_prop_sig` already ran `Mono.strip` on the result.

`tests/custard/RefStrip.fst` is forty abbreviations of `q(n) = q(n-1) /\
q(n-1)`, so the proposition costs 2^40 steps and says `True`.  It appears in
one refinement and nowhere else, and the test runs under
`--custard_norm_budget 20000`: extracting at all is the assertion.

This is the same observation as section 18.3's two hot spots, and the third
time in this round that the extractor turns out to be doing arithmetic on a
proof.  Section 5.1 erases proof-level *values*; what these want is the same
discipline applied to the terms the extractor normalizes in order to make a
decision, and it is worth a pass over every `norm` call in `Extract` asking
what the answer could possibly depend on.

### 19.15 Why the Rust output does not compile, and why it is not the aliases

The reporter closed off the standing hypothesis with a census: of 431
ownership errors from `rustc`, twenty so much as mention `_letpattern`, and
in those the binding is incidental.  The representative one is a function
*parameter*.

The cause is one decision.  karamel logs

```
Pulse.Lib.Slice.slice__uint8_t (FLAT): lifetime=false box=true
```

and emits an owning struct, `{ elt: Box<[u8]>, len: usize }`.  Owning means
not `Copy`, and not `Copy` means every by-value use of a slice is a move.

That it is *owning* is the part that matters, and it is worse than a build
failure.  Because the struct owns its buffer, `split` cannot return aliases
into its parent and deep-copies instead, so a write through either half lands
in a temporary that is dropped.  The reporter silenced the borrow errors with
the `.clone()` calls rustc itself suggests and got zeroes where the C backend
gets `[0, 0, 170, 170, 170, 0, 0, 0]`.  The borrow checker is currently the
only thing standing between this path and a silent wrong answer, which is the
argument for fixing the representation rather than the diagnostics.

The reason karamel gets it wrong is on *our* side of the line.  karamel's
Rust backend recognizes a slice by name and arity:

```ocaml
| TApp ((["Pulse"; "Lib"; "Slice"], "slice"), [ t ]) ->
    Ref (config.lifetime, Shared, Slice (translate_type_with_config env config t))
```

and separately treats the whole `Pulse_Lib_Slice` module as a model, replacing
its definitions with `val`s, when `Options.rust ()`.  Custard monomorphizes
types (section 5.0.1) and emits one flat translation unit, so by the time
karamel sees the program there is no `TApp` of `slice` to match -- there is a
`slice__uint8` struct with a definition -- and no `Pulse_Lib_Slice` module to
model.  Both hooks miss, and karamel falls back to compiling the F* definition,
which is the correct thing to do for C and the wrong thing for Rust.

So the fix belongs here: for `--custard_backend Krml`, `Pulse.Lib.Slice.slice`
and the operations over it have to survive as the abstract type and the
`val`s that karamel is expecting, rather than being monomorphized and
compiled.  That is what `--custard_extern_type` already does for a type whose
definition Custard must not look at, and the operations are what
`[@@custard_extern]` is for; what is missing is that the choice is
target-dependent -- C wants the definition compiled and Rust wants it
abstract -- and Custard's Krml backend does not currently know which of the
two karamel is going to be asked for.  Not done, and not a small change.

### 19.8a A branch of ulib is not a Custard decision

Custard's C output for `Example_Hashtable` carried two one-line wrapper
functions for `FStar.Pervasives.Native.fst` and `snd`, and the obvious fix
was to mark them `inline_for_extraction` in ulib.  It works, and it was
wrong: those two definitions are extracted by *every* F\* user, and marking
them inlineable changed the OCaml the standard pipeline emits repo-wide.
`tests/bug-reports/closed/Bug2595` caught it -- its expected output went from
`FStar_Pervasives_Native.snd` to `__proj__Mktuple2__item___2` -- and it is
the only test that happened to look, which is the argument for reverting
rather than for updating it.

So the wrappers are back, and the principled fix belongs on the Custard side:
`Simplify` should inline a function whose body is a single projection,
which is a local decision about the generated program rather than a change to
what the language extracts.  Not done; noted here so the trade is on record.

### 19.9 What is still open

* The two expensive normalizations of section 18.3, now named.  The next
  step is not a faster normalizer but not asking for those terms: both are
  specification-only and reached through type-level positions.  Sections
  19.11 and 19.14 are the same observation one and two levels up, and
  together they are more than suggestive: three times in two rounds the
  extractor has turned out to be computing with a proof.  What is wanted is
  a pass over every `norm` call in `Extract`, asking of each what the
  answer could depend on.
* `--custard_profile_norm`, which would print the request chain for any
  single normalization over a wall-time threshold.  The reporter has asked
  for it twice and has been bisecting by hand instead.
* Inlining trivial projector functions in `Simplify`, per 19.8a.
* `cbor_det_elim_simple` is the one of the five 19.11 rejections that is not
  a specification: it is real code whose *ghost* index reaches the layout
  pass.  19.11 does not fix it, and whether it needs anything beyond the same
  erasure one level deeper is not yet known.
* The Rust slice representation (§19.15).  Diagnosed and not fixed, and the
  correction that matters is that it is *not* karamel-side: karamel's two
  hooks key on the `Pulse.Lib.Slice.slice` lid and on the module name, and
  whole-program monomorphization erases both.  It is also a
  miscompilation, not just a build failure, so it outranks the rest of this
  list.  Section 20 is the design; the two things it needs that do not
  exist are splitting `--custard_backend Krml` into `KrmlC` and `KrmlRust`,
  and a `Realized` kind that does not rename.
* CDDL error 364: `[@@monomorphize]` does not propagate through a runtime
  parameter in `CDDL.Pulse.Bundle.Base`.  This is the known M7 gap and
  wants M7, not a patch.
* Integration, all three reported together and none addressed: the direct
  backend emits no `.h`, so nothing can call the output; every one of the
  159 functions is exported, with no `static` for those with a single
  caller; and `--custard_split` is OCaml-only.
* karamel's Rust backend, now FStarLang/FStar#4443: 431 ownership errors on
  `cbor_det_serialize` -- 296 `E0507`, 132 `E0382`, 3 `E0505` -- dominated by
  non-`Copy` slice structs dereferenced out of shared references, plus five
  struct literals emitted as bare `match` scrutinees, plus `ERROR translating
  C._zero_for_deref` (which karamel reports while still exiting 0).  All
  karamel-side.

## 20. `Pulse.Lib.Slice` on the Rust path

Section 19.15 established the fault: karamel recognizes a slice by name, and
Custard's monomorphization erases the name.  Sections 20.1 to 20.4 are the
design; section 20.5 is what building it actually took, which was not quite
what 20.3 said.

### 20.1 What karamel is actually asking for

Not "leave the module alone".  Two specific syntactic shapes, and it is worth
being precise about them because they decide the whole design.

The type must reach karamel as an **applied type constructor** carrying its
original lid.  `AstToMiniRust.translate_type_with_config` matches

```ocaml
| TApp ((["Pulse"; "Lib"; "Slice"], "slice"), [ t ]) ->
    Ref (config.lifetime, Shared, Slice (translate_type_with_config env config t))
```

and two further passes (`has_pointer`, and the struct fixpoint that decides
`lifetime`/`box`) match the same shape.  A `TQualified (["Pulse"; "Lib";
"Slice"], "slice__uint8_t")` -- which is what Custard emits today -- matches
none of them, and there is no other channel by which the information could
arrive.

Each operation must reach karamel as a **type application of its original
lid**, `EApp (ETApp (EQualified (["Pulse"; "Lib"; "Slice"], op), ..., ts), es)`,
for `from_array`, `op_Array_Access`, `op_Array_Assignment`, `split`,
`subslice`, `copy` and `len`.  Each becomes a Rust operator or method call --
`Index`, `Assign (Index ...)`, `MethodCall (_, ["split_at"], _)`,
`copy_from_slice`, `len` -- at the *use site*.  The declarations themselves are
deleted outright in step 0 of `translate_files`.

So the requirement is stronger than "do not compile the module".  The type has
to stay **polymorphic**, because the shape karamel matches is an application,
and an application with no arguments is not one.  This is the single hard
constraint on the design, and everything below follows from it.

### 20.2 What Custard already has

Almost all of it, which is the encouraging part.

`Monomorphize.frozen` is a set of type declarations that must stay
polymorphic, and `Monomorphize.freeze` is a transitive closure over it that
already runs from three seeds: the signature of a `DExternal`, a `Realized`
declaration, and an `Imported` one.  A frozen type keeps its name and its
parameters and is not cloned; `is_poly` reads the set and `shape_of` respects
it.  This is exactly the mechanism a slice needs, built for a different reason
(§12.5, M8a) and already load-bearing on the OCaml path.

`PrintKrml` already emits both shapes.  `krml_typ` sends `TApp (n, args)` with
`args <> []` to `K.TApp (lid, ...)`, and `krml_expr` sends `EQual (n, tys)`
with `tys <> []` to `K.ETypApp (K.EQualified lid, ...)`.  Neither is a special
case; they are the general treatment of an applied name.

`lident_of_name` preserves the namespace and only mangles when `n.spec` is
set -- that is, only for a *specialization*.  An unspecialized
`Pulse.Lib.Slice.len` therefore prints as `(["Pulse"; "Lib"; "Slice"], "len")`
already, which is the lid karamel matches, character for character.

What is missing is a reason for any of this to happen, and one thing that is
genuinely absent: the ability to make a decision that depends on which
*karamel target* is downstream.

### 20.3 The proposal

**1. Split the backend in two.**  `--custard_backend` gains `KrmlC` and
`KrmlRust` and loses `Krml`.

The thing that has to be said is not inferrable, and it is worth being clear
about why.  Custard's Krml backend emits a `.krml` file; karamel decides C or
Rust later, from its own command line.  The two want *different programs*: for
C, `Pulse.Lib.Slice` should be compiled from its F\* definition, which is what
it is for and what works today; for Rust it must be absent and abstract.  No
property of the F\* program distinguishes them, so Custard must be told.

The first draft of this section proposed a separate `--custard_krml_target`
flag alongside `--custard_backend Krml`.  Two backend names is better, and
`tests/extraction/backends` is the argument: the matrix already has
`custard-krml-c` and `custard-krml-rust` as distinct rows, and they currently
pass *identical* F\* flags and diverge only in what they hand to karamel
afterwards.  The two targets are already two things everywhere except in the
one place that has to know.

It is also the honest shape.  A `.krml` file built for Rust cannot be compiled
to C -- the slice is gone from it -- so this is not a modifier on a backend,
it is a different backend that happens to share a printer.  A flag would have
let the two be set inconsistently and would have needed the `.cui` header
(M10a) to police the combination; a name cannot be.  `uh_backend` already
records the backend and already refuses a mismatch, so the existing check
covers this for free.

`EnumStr` makes an unknown name an error at parse time, so the removal of
`Krml` is diagnosed at the command line rather than by `Driver`'s fallthrough.
Six call sites in the tree pass `--custard_backend Krml` and all six know
which target they are building for, four of them in the very Makefiles that
already say so in their rule names.

Mechanically this is a predicate, not a fork: `Driver`'s dispatch, the `.krml`
extension and `PrintKrml` want "is this a Krml backend", and only the freeze
seeding of item 3 wants to tell them apart.  So `Options.custard_backend_krml
()` alongside the two literal comparisons, rather than duplicated branches.

**2. A rule kind, `Rule_slice`, or more honestly `Rule_krml_model`.**

Section 8.2's `Rule_realized` is nearly right -- "a hand-written module in the
target language defines this; keep the declaration for its shape, do not emit
it" -- and differs in exactly one respect: `Rule_realized` renames every
reference to the realization's own name, and here the name is already correct.
So the new kind is `Rule_realized` minus the renaming, and it should be
implemented by giving `Rule_realized` an optional target name rather than by
copying it.

The list is data, not code, for the same reason `extern_types` is empty in
§8.2: which modules karamel models is a fact about karamel, and today it is
one module.  A `--custard_krml_model <lid>` flag, with `Pulse.Lib.Slice`
pre-registered under `KrmlRust`, keeps the fact where it can be corrected
without a rebuild.

**3. Freeze the type.**

`Monomorphize.freeze_realized` currently reads
`Options.custard_backend () = "OCaml"`, with the comment that the C backends
realize nothing.  That premise is what changes: `KrmlRust` realizes exactly
one module.
So the guard becomes a question about the *program* -- is this declaration
`Realized`, whatever the backend -- and the backend-specific part shrinks to
which declarations get marked.

Freezing is already transitive, which handles the consequence automatically: a
struct with a `slice` field must not be cloned per-instantiation either,
because karamel's `lifetime`/`box` fixpoint has to see the `TApp` inside it.
The existing closure does that without being asked.

**4. Emit the operations as externals.**

`Extract` stops at a `Rule_realized` declaration today (`Extract.fst:1240`,
`2391`), keeping the signature and not the body.  Sending those to
`PrintKrml` as `DExternal` rather than dropping them gives karamel a
well-typed program; `EQual (op, [t])` at each use site is then already an
`ETypApp` and already matches.

A polymorphic `DExternal` needs karamel's `-fallow-tapps`, which the Rust
pipeline sets anyway (`Checker.ml:129`, `Monomorphization.ml:236`) -- this is
how every karamel model with type parameters already works, so it is a
documented configuration rather than a new demand.

**5. Reject the mixture.**

Under `--custard_backend KrmlRust`, a `slice` reaching `Layout` or the
monomorphizer un-frozen is a bug in the freeze seeding, and should say so
rather than producing the struct silently.  This is §19.13's rule: the failure
mode we are fixing was a *silent miscompilation*, and the only reason it was
caught is that the borrow checker happened to object.  Something in Custard
should object first.

### 20.5 What building it took

All five items of 20.3 are built and `tests/custard/pulse/PulseSlice.fst`
compiles to Rust that borrows, runs, and agrees with the C column.  Four
things the design did not anticipate, each found by a failure rather than by
reading:

**A model is not a realization, and needs its own flag.**  20.3 item 2 leans
on `Rule_realized` and the first implementation went further and reused
`Realized` itself, dropping the type declaration of anything carrying it on
the karamel path.  That deletes `FStar.Pervasives.Native.tuple2`, which is
realized in OCaml and has nothing to do with Rust.  The two facts are
genuinely different: a realization is hand-written *OCaml*, so on the karamel
backends the declaration is still Custard's to emit; a model is the target
compiler's on the backend it applies to and never is.  Hence a separate
`Modelled` decl flag, set by `Extract` alongside `Realized`, and read by
`PrintKrml` and by the freeze.

**A modelled value must still be emitted, as an external.**  Dropping the
`DExternal` for `Pulse.Lib.Slice.from_array` is the obvious reading of "leave
it to karamel", and karamel refuses it: `Warning 2: Reference to
Pulse.Lib.Slice.from_array has no corresponding implementation`, fatal, from
the checker, which resolves every reference *before* the Rust pass rewrites
any of them.  Only the *type* declaration is dropped.

**A modelled external's type variables must be `TBound`, not `TAny`.**
`PrintKrml` sets `tvars_any` for an external because a hand-written
realization really is polymorphic and C's answer to polymorphism is
`void*`.  For a model that is fatal --- `Failure("unexpected: [type] no casts
in Low* -> Rust")` --- since the reference is going to become a Rust operator
and Rust has no cast from `any`.  The variables the external binds are the
right answer and reach karamel as `TBound`.

**Tuples must be real tuples, and `krml` needs `-fkeep-tuples`.**
`Pulse.Lib.Slice.split` becomes `split_at_mut`, whose result karamel
destructures with `OptimizeMiniRust.retrieve_pair_type`; that function
*crashes* on anything but `MiniRust.Tuple [t; t]`.  So on `KrmlRust`,
`FStar.Pervasives.Native.tupleN` and `MktupleN` are modelled too and print as
the IR's `TTuple`/`ETuple`/`PTuple` --- which have existed all along, and
which `PrintKrml` has always printed; what was missing was any reason to
produce them, a struct being what C wants and the C backends being all there
was.  Only the tuples, not the whole of `FStar.Pervasives.Native`: `option`
is in the same module and karamel compiles it happily.  And without
`-fkeep-tuples`, `Monomorphization.visit_TTuple` has already turned the tuple
into a struct by the time the Rust backend looks at it.

The whitelist of 20.4 is built as `Builtins.is_known_krml_model_op`, checked
in `PrintKrml` at the point of no return, and lists exactly the seven
operations `AstToMiniRust` matches.  A module named by `--custard_krml_model`
is not checked: that flag is the caller's assertion and is taken at its word.

One thing the test exposed that is *not* about slices.  `Pulse.Lib.Slice.split`
is polymorphic and returns a tuple, so with types compiled uniformly (§6) the
`.krml` for the C column holds `tuple2<slice<'t>, slice<'t>>`: a type
application whose arguments are not ground.  karamel's own monomorphizer only
instantiates closed applications, so its checker then reports `tuple2` as an
undefined type.  `--custard_monomorphize_types true` sidesteps it and the test
passes it on that column.  Pre-existing, and unrelated to §20; `PulseSlice` is
simply the first test in the suite to return a tuple from a polymorphic
function.

### 20.6 A slice in a field, and two more from round 9

The round-9 report took `--custard_backend KrmlRust` to EverParse and got 436
Rust errors down to 28, with the miscompilation itself gone.  Two of the
remaining classes are worth recording, because one is Custard's and one is
not, and telling them apart took a reproduction.

**`_` in expression position** is Custard's.  `PrintKrml` compiled an `ESeq`
whose first component is not `unit` into a `let`, karamel requiring every
element of a sequence but the last to be of unit type, and named that binder
`_`.  karamel's use analysis then finds the binder unread and rewrites the
binding into `let b = e1 in ignore b` -- and its Rust backend prints a
binder's name verbatim, so the reference came out as `ignore(_)`, and `_` is
not an expression in Rust.  The C backend renames, which is why this had gone
unnoticed.  The binder now gets an ordinary name, freshened against the
enclosing scope because `find` resolves a reference by the first matching
name and `Rename` gives a local its bare source spelling.  Visible in
`PulseHashTable`, so it needed no new test.

**A slice in a field of a returned struct** is karamel's, and the reporter's
diagnosis of it was close but not right.  He read `cbor_array` and
`cbor_tagged` as "structurally identical types that disagree with
themselves", one emitting `&[cbor_raw]` and the other `Box<[cbor_raw]>`.
They are not identical: `AstToMiniRust` translates `TApp (slice, [t])` to
`Ref (..., Slice ...)` unconditionally and has no path from a slice to a
`Box`, so a field that came out `Box<[T]>` was a *buffer* in the IR and not a
slice at all.  That is a question about the F\* source, not about the backend.

The real defect is the other half, and it is exactly the `E0106`s.  karamel
sorts a struct that holds pointers into one of two disjoint sets
(`compute_struct_info`): **returned** by value, so it owns its pointees and
they become `Box`; or **not returned**, so it borrows them and the struct
gains a lifetime.  A slice belongs to neither.  It is a borrow by
construction and cannot be owned, so when a struct holding one lands in the
returned set it gets `box=true, lifetime=false` and its slice field is
emitted as `&[T]` inside a type that binds no lifetime.

`tests/custard/pulse/PulseSliceRec.fst` is three declarations that reproduce
it -- a record with a slice field, a variant with one, and a variant that
reaches itself through one, which is `cbor_raw`/`cbor_array` in miniature.
All three are correct while the struct is only ever passed as an argument:

```rust
pub struct view <'a> { pub bytes: &'a [u8], pub tag: u8 }
pub enum tree <'a> { Leaf { _0: u8 }, Node { _0: &'a [tree <'a>] } }
```

Adding one total function that returns a `view` by value, and nothing else,
is enough to flip it:

```rust
pub struct view { pub bytes: &[u8], pub tag: u8 }   // E0106
```

`krml -fno-box` empties the returned set and every such struct gets its
lifetime back; the test passes it, compiles, and runs.  That is a workaround
and not the fix -- it also declines to box structs that genuinely should be
-- but it costs nothing here, since a slice is the only pointer these
programs hold.  Reported as karamel#753.

### 20.4 What this does not solve

`Pulse.Lib.Slice` has around twenty `val`s and karamel translates seven.  The
rest are ghost (`pts_to`, `is_split`, `share`, `gather`) and erase before any
of this, which is why the count works out -- but that is a property of today's
`Pulse.Lib.Slice`, not a guarantee.  A future runtime operation would extract
as an external karamel has no rule for, and fail at the `ETApp` with no useful
message.  The check in item 5 should therefore be a *whitelist* of the seven,
not a check that the module was frozen.

`Pulse.Lib.Array` and `Pulse.Lib.Reference` have the same shape and are not
addressed.  The mechanism generalizes; the entries do not exist.

And the honest limitation: this makes Custard's Krml backend carry a model of
what karamel's Rust backend recognizes, in two places that must agree and have
no way to check that they do.  The alternative -- karamel recognizing a
*monomorphized* slice by name prefix -- was considered and is worse: it makes
a name-mangling convention into an interface, and Custard's mangling is
already something §12.7 wanted the freedom to change.  A shared declaration of
the seven lids, read by both, would be better than either, and is the thing to
build if a second module ever needs this.

## 21. A projector whose field is a function

Master made projectors and discriminators *declaration-only* (#4389): F\*
emits the `val` and no longer a `Sig_let`, leaving it to each extraction
backend to inline the projection or emit a record access.  Custard already had
the machinery, `Extract.assumed_projector_lb`, written for
`[@@no_auto_projectors]` -- it rebuilds the definition `TcInductive` would
have built, a match on the projectee returning the chosen field, which §5's
inlining then collapses to one `EProj` or one `EDiscrim`.  What changed is
that this path went from an attribute nobody uses to the path *every*
projector takes, and it had a bug that the narrow case never exposed.

It took the projectee to be the **last** binder of the projector's type.  That
is right only when the projected field is not itself a function.
`U.arrow_formals_comp` flattens the whole spine, so for

```fstar
type iter_t = { contents: U64.t; impl_validate: U64.t -> bool; ... }
```

the projector's type is `iter_t -> U64.t -> bool` and the last binder is the
field's own argument.  The synthesized match then scrutinized *that*, and

```fstar
let run (i : iter_t) : U64.t =
  if i.impl_validate i.contents then i.impl_parse i.contents else 0uL
```

came out as `i.contents.impl_validate` -- a miscompilation, not a rejection,
and the interesting kind: the three CI failures it produced were a C one
("the field `impl_validate` has no C representation ... its owner is not a
declared type"), a Pulse one ("the constructor `Mkht_t` ... belongs to no type
declaration in the program") and an *OCaml type error* in the generated code,
none of which names a projector.

The projectee is now found by its type: the first binder headed by the
inductive that the constructor belongs to.  Everything before it is a
parameter or an index, everything after belongs to the field, and the trailing
binders are kept with the match applied to them -- verbatim the shape F\*
itself used to generate here, and the one `Simplify.eta_reduce` already exists
to clean up.  Dropping them instead would leave the definition with fewer
binders than its declared type, which is §19.4's failure in the other
direction.

Also from the merge: `FStar.Tactics.MkProjectors` is deleted, and
`src/custard/entrypoints.txt` named it.

## 22. Operators get their names changed underneath us

Master made operator name mangling uniform: an operator becomes an identifier
by naming each of its characters and joining the names with underscores, with
no special cases, so `( + )` is `op_Plus` rather than `op_Addition` and
`( .() )` is `op_Dot_Lparen_Rparen` rather than `op_Array_Access`.  Mangling no
longer depends on arity either, so prefix minus is `( ~- )` and `op_Minus` now
means *binary* subtraction.

Custard reads and writes those names in four places, and each had to move.

**What Custard recognizes.**  `Builtins.prims_rule` keys the boolean
connectives on their mangled names, and all five changed: `op_Amp_Amp`,
`op_Bar_Bar`, `op_Equals`, `op_Less_Greater`, and `not` -- which was
`op_Negation` and is now just the ordinary function it always was.  The same
for `Pulse.Lib.Vec` and `Pulse.Lib.ArrayPtr`'s indexing.  These are silent
failures if missed: an unrecognized name is not an error, it is an ordinary
call to something C has no definition for, so the failure surfaces at link
time or, worse, as a `void *` signature.

**What Custard emits to karamel.**  karamel recognizes a handful of F\*
definitions by name and spells them the old way, because it is a separate
repository and cannot be updated in the same commit.  Master added
`FStarC.Extraction.Krml.krml_compat_name` to rewrite them on the way out;
`Builtins.krml_compat_name` is its twin, and the two tables have to agree.
It is applied in `PrintKrml.lident_of_name`, which every value name passes
through -- mapping a reference but not the declaration it resolves to renames
a use away from its own definition, and karamel then reports the definition as
missing.  Before the specialization suffix, since the table is keyed on the
source name and `op_Array_Access__t` is not in it.

Master's table was missing one entry, `op_Star`.  It is the only Prims operator
whose old name is not recoverable from the new one by the same rule as the
rest -- `Multiply` against `Star` -- so it was the one that got overlooked, and
`Prims_op_Star` was undefined in the generated C.  That was finding #6 in
`tests/extraction/backends/FINDINGS.md`, an `XFAIL` in two columns; adding the
entry fixes both.

**What Custard emits to OCaml.**  `PrintOCaml` names the Prims arithmetic
functions directly, and the generated `Prims.ml` now defines them under the
new names.  The direct C backend gets no mapping and wants none: nothing
downstream matches on those names, so `Pulse_Lib_Slice_op_Dot_Lparen_Rparen`
is simply what the function is now called.

**Two entry points that moved.**  `FStarC.Parser.AST.compile_op'` is gone,
uniform mangling having removed the arity argument that made it separate;
`compile_op` is what remains.  And `Pulse_RuntimeUtils.ml` picked up a use of
`FStarC.Syntax.Syntax.uu___is_Unresolved_name`, which is the interesting one.

### 22.1 Custard's error codes moved up by one

Custard's diagnostics were numbered 362-369 on this branch, taking the next
free codes at the time.  Master has since assigned 362 to
`Error_AmbiguousName`, from the type-based overloading work, and that number
is not free to move: `tests/overloading/strict/StrictDuplicate.fst` demotes it
with `--warn_error +362`, and the book names it by number in
`doc/book/PoP-in-FStar/book/part1/part1_modules.rst`.  A published number in
user-facing documentation outranks a branch-local one, so Custard's codes
moved to **363-370** and `Error_AmbiguousName` keeps 362.

The numbers in `FStarC.Errors.Codes.fst` are written explicitly rather than
derived from position, so this is a relabelling and not a reordering.  It
touches every place the numbers are spelled out: the `CODE_*` variables that
`tests/custard/Makefile` greps the diagnostic for, the `--warn_error @367` of
the `--custard_warn_any` tests, and the prose here.  Nothing else in the
compiler dispatches on a code's number.

The cost is that the numbers cited in the bug reports of sections 18 through
21 are one lower than the ones the compiler now prints; they have been updated
here, and a reader working from an older report should add one.

### 22.2 A root that is a discriminator

A projector or a discriminator is `Inline`: it is substituted at its uses and
never emitted, because it is one field read or one tag test and a declaration
for it would be a call where an access belongs.  That is right for everything
inside the extracted program, and wrong for one that is named as a root.

A root exists precisely because something *outside* the program calls it --
`--custard_entrypoints` is how the hand-written OCaml under `pulse/src/ml`
reaches the compiler, by OCaml name, through no request Custard can see
(section 12.13).  That caller has nothing to inline into.  Adding the name to
`pulse/src/custard-entrypoints.txt` was therefore not enough on its own: the
declaration was extracted, marked `Root`, and then dropped anyway.

Two changes, because the flag is read in two places.  `Extract` now records
every root before any of them is marked -- a root is reached like anything
else, and a discriminator that some *other* root gets to first would be
extracted, marked `Inline` and cached before its own turn came -- and does not
mark a rooted projector or discriminator `Inline`.  `Simplify.inline_decls`
keeps a declaration that is `Root` even when it is `Inline`, which is what
actually makes it survive.  Uses inside the program are still substituted;
only the declaration stays.

## 23. "It compiles" is not an acceptance criterion

Every backend test in this suite up to now asserted one of two things: that
extraction produces the output we expected, character for character, or that
the output compiles with the warnings turned on.  Both are worth asserting
and neither is a specification.  A backend can emit code that compiles
cleanly, matches a golden file nobody has re-read in months, and computes the
wrong answer -- and section 19.15 is the case in point, where karamel
compiled a borrowed slice as an owning `Box` and writes through it were
silently discarded.  Nothing in the suite failed, because nothing in the
suite ran anything.

`tests/custard/CborBoundary.fst` and `tests/custard/pulse/CborBoundarySlice.fst`
are the answer: two reduced deterministic-CBOR well-formedness checkers,
generated from one corpus of 48 boundary vectors whose expected results come
from an independent Python model of the same grammar, so that the table of
answers is not the parser under test agreeing with itself.  Each `main`
writes every vector, runs the checker, compares against the model's answer
and reports through its exit status.  `CborBoundary.md` documents the corpus.

### 23.1 Line coverage is the wrong thing to minimise against

The corpus is small because it was made small deliberately, and the way it
was made small is the part worth keeping.

Greedy set cover over line coverage reduces a 12,110-input random corpus to
**28 inputs with identical line coverage** -- a 400x reduction, and an
attractive one.  It is also 13% worse: against 135 mutants of the extracted
C that the full corpus kills, the 28-input set kills 118.  The lines are all
executed; they are simply never executed with the operand values that
discriminate.  Reducing against *mutants* instead gives a set of the same
order of magnitude that reproduces the full corpus exactly, and does so on a
held-out mutation family it was not fitted to -- 152 of 152, against 57 of
152 for the coverage-reduced set at essentially the same size.

So the rule this directory encodes is: **equal coverage is not equal defect
detection, and coverage is not the signal to minimise against.**  Anyone
proposing to shrink this corpus should be pointed at those two numbers
first, because the obvious shrink was tried, measured, and was silently
worse.

The corpus that resulted strictly dominates the random one it came from: no
mutant that the 680 KB corpus catches is missed by the 13 KB one, and its
line coverage is a strict superset.  The vectors that survive minimisation
are visibly the boundary corpus -- `63e0a080`, `63ed9fbf`, `64f0908080`,
`64f48fbfbf`, `62dfbf`, `617f` -- because those are the ones that
discriminate.

Two measurement mistakes are recorded in `CborBoundary.md` because both
would otherwise be made again.  A 40-mutant sample said the small corpus was
already at parity; at 300 mutants that collapsed to 126 of 135, so the
parity result was a small-sample artifact that would have shipped a worse
corpus.  And a mutation generator that selected lines from anywhere the two
variants shared text was corrupting the *embedded vector constructors* --
mutating the test data rather than the parser, and inflating the kill count
with trivially-detected mutants.  `mutants.py` therefore reads the functions
it may mutate from a per-module `.parsers.txt`.

Everything runs under `-fsanitize=address,undefined -fno-sanitize-recover=all`,
by default rather than on request, because one mutant was otherwise detected
only when binary layout happened to make its memory unsafety observable.  A
test whose outcome depends on layout is not a test.

### 23.2 Two representations, one corpus

The two checkers differ only in how the input is represented, and that is
why both are kept.  `CborBoundary.fst` consumes a `ref`-linked cons cell,
which is what a pure-F\* module can have; it needs no Pulse, and so it is the
one that runs under stage1 and stage2 as well as stage3.
`CborBoundarySlice.fst` consumes a `Pulse.Lib.Slice.slice byte` over a stack
array, which is what EverParse's parsers take, and is the only one of the
two that can drive the Rust column at all.

That difference is not cosmetic, and the evidence is a mutant.  Porting the
checker onto a buffer exposed a hole in the corpus that the list version
could not have: `peek` was never called at `i == len` by any of the 40
vectors then in the corpus, so no vector was truncated *inside a header's
argument bytes*, despite truncation being one of the four classes the corpus
claimed to cover.  A list running off its end returns `None` structurally,
so the bounds check that the buffer version needs did not exist to be
mutated.  The corpus grew to 48 by adding the principled class -- one
truncated-argument vector per argument width -- rather than the individual
witness, which would have been fitting to the held-out family and would have
destroyed its value.

The constraint that separates the two is a **staging** one and not a
representation one: a `#lang-pulse` module cannot be parsed by stage1 or
stage2, which have no Pulse syntax extension, so it cannot live in
`tests/custard/` without breaking `test-1` and `test-2`.  That is the reason
`tests/custard/pulse/` exists, and it is worth stating because the plausible
reading -- that Pulse's array abstractions are unavailable and therefore a
contiguous buffer is unreachable from direct-to-C -- is false.  Both
`let mut arr = [| ... |]` and `Pulse.Lib.Vec.alloc` extract to a stack array
and a `{ elt; len }` slice in C, and to `&mut [u8]` in Rust.

### 23.3 The Pulse Custard tests now run in CI

`tests/custard/pulse` was reachable only by hand: `_test_pulse` ran
`pulse/test/` and `pulse/share/pulse/examples/`, not this directory.  So
`PulseSlice`, `PulseSliceRec` and `PulseHashTable` -- including the Rust
column that section 20 exists for, and the `Box` regression test of section
20.6 -- guarded nothing.  The root `Makefile`'s `_test_pulse` now also runs
`tests/custard/pulse/`, which `make ci` reaches through `test-3`; the
directory's own `Makefile` already gates its krml and Rust columns on those
tools being present.

### 23.4 A green result that is not evidence

Section 24 gave the direct-to-C backend a header, and the generated source
opens with `#include "<Module>.h"`.  `cbor-corpus/mutants.py` writes each
mutant into `_output/mutants/` and compiled it there, where that include does
not resolve.  Every mutant became uncompilable and both adequacy figures
collapsed to

```
family=ops     killed 0 / 0  (uncompilable 46)
family=consts  killed 0 / 0  (uncompilable 46)
```

Adding the `.dc`'s own directory to the include path restores 46/46, 46/46,
48/49 and 46/59 exactly (#4484).

The include path is the trivial half.  The half worth recording is the
**failure mode**: the script did not error out.  `killed 0 / 0` is a pass
under any "did it fail?" reading, so the adequacy study would have gone on
reporting success while measuring nothing -- which is section 23's own thesis
turned around and pointed at section 23's own tooling.  A green result is not
evidence unless something would have gone red.

So the count is now fatal rather than reported.  An uncompilable mutant is not
a weak test but an absent one, and it is always a defect in the script or in
the backend, never a property of the corpus: there is no reading of "this
mutant does not build" that the study should tolerate.  A zero-mutant run is
fatal for the same reason, since an empty `PARSER` list would otherwise report
`killed 0 / 0` too.

## 24. The unit is a header and a source

Until now `--custard_backend C` wrote one file.  Everything in it had external
linkage, and there was no declaration of anything for a caller to include, so
a program that wanted to call an extracted function had to write the
prototypes out by hand, and a program that linked two extracted units risked a
duplicate symbol for every name they happened to share.  Neither is a
theoretical worry: the DICE example (`pulse/share/pulse/examples/dice`) links
Custard's C against hand-written C, and the reason the direct backend has not
been offered as a drop-in replacement for a krml-produced `CBORDet.c` is that
a drop-in replacement has to come with `CBORDet.h`.

`print_program` now returns a pair, and the driver writes `<stem>.h` beside
`<stem>.c`, where the stem is the output path with its extension removed --
extension-agnostic on purpose, because the test suite asks for `-o
_output/Foo.dc` and would otherwise get `Foo.dc.h`.

### 24.1 What is public

The IR has had a `Private` flag on declarations since M2, and `PrintC` read
it.  Nothing ever produced it.  That is the whole reason every definition had
external linkage: the flag was live in the printer and dead in the pipeline,
and a test that greps for `static` would have been the only way to notice.

Rather than start producing it, storage is derived from the flag that already
means what we need.  A declaration is **public exactly when it is a `Root` and
not the `Entrypoint`**; everything else gets `static`.  This is not a new
notion of visibility, it is the one the user already stated: a `Root` exists
because `--custard_entry` or `--custard_entry_module` named it, and naming a
declaration as a root is precisely the claim that a caller Custard cannot see
will call it.  Everything else is reachable only from inside the unit -- that
is what §6's dead-code elimination proved when it kept the declaration at all.

The entry point is excluded because it is a root for a different reason.
`Driver.run_phases` adds `--custard_main`'s target to the roots so that the
common case needs only one option, but that root exists to keep the
declaration alive through DCE, not to offer it to a linker; the generated
`main` calls it from inside the same file.  The imprecision this leaves is
that `--custard_entry F --custard_main F` does not export `F`.  That is
deliberate and, if it ever matters, the fix is to distinguish the two roots
rather than to widen the test.

There is no `-Wunused-function` exposure in making things `static`, because
DCE runs first: every declaration that reaches the printer is reachable from
a root or from the entry point, so a `static` one is always called within its
own file.  The four suites compile with `-Wall -Wextra -Werror` and agree.

### 24.2 What is in the header

The header carries the unit's **whole type language** -- every forward
declaration, `typedef`, `struct` body and extern-type include -- and only the
public prototypes.  The asymmetry is deliberate.  `struct` and `typedef` have
no linkage, so emitting all of them costs nothing and collides with nothing,
whereas a reachability-trimmed subset buys an incomplete header: a public
function whose argument is a struct we decided not to emit produces "field has
incomplete type" at the first include, and the trimming would have to
re-derive, per public declaration, the transitive closure the `Layout`
fixpoint already computed.  Prototypes are different: a prototype *is* the
linkage claim, so the private ones stay in the source, where they are still
needed to order mutually recursive definitions.

A parameterless definition is a C variable, not a function.  Its definition
stays in the source, `static` if private, and the header gets `extern <type>
<name>;` -- the one place where the header's spelling is not the source's.
`custard_init_globals` is public and gets a prototype whenever there is a
non-constant global initializer to run, since a caller who links the unit is
the one who has to call it.  Read that as an obligation of *memory safety* and
not of freshness: a global of function-pointer type is null until it runs, and
a public entry point that reaches one jumps through null.  Section 27 removes
the largest class of definitions that had no business being globals in the
first place, but the obligation stands for the ones that remain.

The source `#include`s its own header, before anything else it emits.  This is
what makes the header *checked* rather than merely shipped: a prototype that
disagrees with its definition is a compile error in the unit that generated
both, not in some downstream consumer.  The include guard is `__<STEM>_H`,
from the sanitized upper-cased stem.

### 24.3 Testing

`tests/custard/Makefile`'s `CGREP_`/`CNOGREP_` assertions now search `$@` and
`$(basename $@).h` together, so an existing expectation about the C output
keeps holding wherever the declaration ended up, and a test can pin the split
by asserting on one file that a name is absent from the other.
`pulse/mk/custard-test.mk` gained a no-op rule making the `.h` depend on the
`.c`, which is enough for `mk/test.mk`'s generic `%.diff` rule to pick up the
ten new `*.h.expected` goldens.

The shape the change produces, on `Example_Slice`: the header is the guard,
the four standard includes, `custard_unit`, the slice and tuple types, and
exactly one line of prototype, `void Example_Slice_test(uint8_t *arr);`; the
source has fourteen `static` declarations and one that is not.  On DICE, 144
declarations become `static` and the six `--custard_entry` names are the six
that do not.  On a `--custard_main` program such as `CRecType`, nothing is
exported but `main`.

`PrintKrml` still maps `Private` to karamel's `Private` qualifier, so the flag
stays in the IR; it is simply not what the direct backend consults.


## 25. An argument goes missing between two definitions

Round 19 of the EverParse report reduced everything still blocking CDDL to
one defect, with an eleven-line module that carries its own control:

```fstar
let f (x: bool) (y: bool) : bool = x && y   (* arity 2 in the source *)
let g : bool -> bool -> bool = f            (* arity 0 in the source *)

let call_f (a: bool) (b: bool) : bool = f a b
let call_g (a: bool) (b: bool) : bool = g a b
let call_g_partial (a: bool) : (bool -> bool) = g a
```

`g` came out right -- a real two-argument C function -- and `call_g` came out
as `bool (*Wrap_call_g(bool a))(bool)`, one parameter short, returning a
function pointer, and calling `Wrap_g(a)`.  Four `cc -std=c11` errors before
`-Wall`, two of them "too few arguments to function `Wrap_g`" against a
prototype the same run had just emitted.

The sharpest part of the report is that **`call_g` and `call_g_partial`
produced byte-identical C**, although one is a full application in the source
and the other a partial one.  The second argument of the former was simply
dropped.  So this is not only "the IR pretends C has partial application":
an argument goes missing on the way, and the IR is wrong before the backend
sees it.  C refuses the result, so it could not have misbehaved silently
here -- but that is C's doing, not ours.

### 25.1 Why the argument goes missing

Two passes, each correct alone.

`eta_reduce_decls` (section 7.3) shortens `fun a b -> g a b` to `fun a -> g a`
-- one step, because the rule strips one trailing binder at a time and the
result is no longer of the form `fun bs -> h bs`.  That is a legitimate
rewrite and OCaml is happy with it.  `eta_expand_decls` exists precisely to
undo it for C, since a definition whose result type is still an arrow is a
partial application C cannot express.

But `eta_expand_decls` bounded the expansion by a table of arities computed
**once, from the program as it found it**.  `g` is parameterless in the
source, so the table recorded arity 0 for it, so `call_g`'s body `g a` looked
like an *over*-application already and was owed nothing.  Meanwhile the same
pass, in the same sweep, gave `g` its two binders.  The table was stale the
moment the pass began, and the staleness is exactly one link long -- which is
why the control `call_f` is correct (`f` has its binders in the source) and
why every variant the reporter tried was clean except this one.

The fix is to run the pass **to a fixpoint**: each round recomputes the
arities and so learns what the previous round established, and the chain
`f` → `g` → `call_g` → `h` resolves one link per round.  Termination is
not a question of taste: a round can only *add* binders, and never more than
`arrow_arity dl_ret` of them, so the total binder count is monotone and
bounded; the fuel is the chain length.

This also fixes `call_g_partial`, which *is* a partial application in the
source.  Top-level eta-expansion is free -- the new binders become C
parameters, not captures -- so there was never a reason to reject it; the only
reason it was rejected is that the same stale table denied it the same
argument.

### 25.2 The backend now refuses a call it cannot spell

The bug reached a C compiler rather than a diagnostic because `PrintC` prints
`EApp (h, args)` as `h(args)` without ever asking how many arguments `h`
takes.  An under-applied call is then a call with too few operands, and an
over-applied one -- applying a call's *result*, which is a separate
application node -- is a call with too many.  Both are valid IR and neither is
C.

`PrintC` now records the arity of every definition and external, after the
dropped parameters of `keeps` are removed, and refuses a call that does not
match.  Under-application is error 368, "no C representation", because it is a
fact about the source, and the message names the `[@@@monomorphize]` remedy;
over-application is the "malformed IR" refusal, because it is a fact about the
compiler.  The point is not that these should happen -- after 25.1 none of
them do, across five suites -- but that the next one should be reported here,
in Custard's vocabulary, rather than as "too few arguments" against a
generated prototype three tools downstream.

### 25.3 What is not fixed, and deliberately

A definition whose body is a *call that returns a function* stays a global
variable:

```fstar
let ap (phi: (bool -> bool -> bool)) : (bool -> bool -> bool) = phi
let e : bool -> bool -> bool = ap band
```

becomes `static bool (*GlobalVar_e)(bool, bool);` initialized in
`custard_init_globals`.  This compiles and runs correctly, and the reporter
raised it as a quality matter rather than a bug.  Expanding it to
`e x y = ap band x y` would re-evaluate `ap band` on every call, which is the
hazard `cheap_expr` exists to prevent and section 13.5 records: `ap` happens
to be the identity here, but the pass cannot tell that from the shape, and a
body that computes before returning a function must not be duplicated into
every call site.  The cost of the current shape is a mandatory
`custard_init_globals()` before first use -- which section 24 now makes a
caller's documented obligation -- and one indirect call per use.  If the
combinator is inlinable, `inline` and `reduce` fold `ap band` to `band` and
the definition becomes a plain name, which *is* expanded.

Likewise, a lambda that captures a local and is stored in a record field --
which is what every EverParse bundle is -- remains an honest error 368.  The
remedy is the one the diagnostic names and round 19 confirmed on the real
code: `[@@@monomorphize]` on the *function-typed parameters* of the
combinator, not on the definition that calls it.  Marking `f12`, `f21` and
`eq'` in `CDDL.Pulse.Bundle.Base.mk_eq_test_bij` lifts the lambda and the
module reverifies unchanged.  Auto-marking function-typed parameters would
remove the need for the annotation and is the strongest argument yet for the
M7 defunctionalization work; it is not a prerequisite for it.

### 25.4 Tests

`tests/custard/CEtaChain.fst` is the reporter's module with a fourth link
added -- `let h : bool -> bool -> bool = call_g` -- so that a single round of
expansion cannot pass it, and with `main` checking its own answers so that the
suite runs the binary rather than merely compiling it (the M8b criterion).  It
greps for `CEtaChain_g(bool` and against `(*CEtaChain_g)`, which is the
difference between the fixed and the broken output.
`tests/custard/CLamField.fst` is the record-of-function-fields rejection,
expecting 368; it is separate from `CNoClosure` because that one captures a
let-bound local and this one captures a parameter and stores the result in a
structure.


## 26. Two more ways to lose an argument

Section 25 fixed the arity chain and added a check meant to catch the next
one.  Round 20 of the EverParse report found two the check did not catch, one
of which it *had* caught in a different program -- which is how the report
found it.  Both are ten to fifteen lines, and together they were the whole of
what still stood between CDDL and a clean build.

### 26.1 A variable is not a definition

```fstar
let ap (phi: (bool -> bool -> bool)) : (bool -> bool -> bool) = phi
let band (a: bool) (b: bool) : bool = a && b
let e : bool -> bool -> bool = ap band
let call_e (a: bool) (b: bool) : bool = e a b
```

`call_e` came out with one parameter, calling `e(a)` against a two-parameter
function pointer -- the section 25 symptom exactly, unfixed by the section 25
fix.

The reason is section 25.3, the thing we had just agreed was a quality matter
rather than a bug.  `e`'s body is a *call* that returns a function, so
`cheap_expr` declines to expand it and it is lowered to a **variable** of
function-pointer type.  Both the arity table that drives eta-expansion and the
backend's new call-arity check recorded *definitions*, keyed on binder count.
A parameterless definition has no binders, so both read `e` as arity 0: the
expansion concluded `call_e` was owed nothing, and the check concluded there
was nothing to check.

So the variable/function lowering turned out to be load-bearing for
correctness, in a way nothing intended.  Becoming a variable is what made the
callee invisible to the arity machinery, and the reporter is right that this
changes 25.3's status: the guard itself is still correct -- re-evaluating `ap
band` at every call site is a real cost -- but "it is only a quality matter"
was wrong.

Both tables now read a parameterless arrow-typed definition's arity off its
**type** rather than its binder list, because that is what the emitted object
accepts: `static bool (*e)(bool, bool)` takes two arguments in one call.  This
also makes the two tables agree with each other and with the printer, and it
happens to make the fixpoint of section 25 converge one round sooner, since a
definition about to be expanded already advertises the arity it will have.

The shape worth keeping is the reporter's second module, which is the first
with `main` deleted and `call_e` as the root.  Nothing then over-applies
`call_e`, so there is no downstream symptom at all: extraction exits 0 and the
only complaint is the C compiler's.  `tests/custard/CVarArity.fst` covers both
by making `call_e` a root *and* calling it from `main`.

### 26.2 An arrow behind two abbreviations

```fstar
let eq_test_for (#t: Type) (x1: t) : Type = FE.restricted_t t (fun _ -> bool)
let eq_test (t: Type) : Type = FE.restricted_t t (fun x1 -> eq_test_for x1)

let mk_eq_test (#t: Type) ([@@@monomorphize]phi: (t -> t -> bool)) : eq_test t =
  FE.on_dom t (fun x1 -> FE.on_dom t (fun x2 -> phi x1 x2))
```

`mk_eq_test`'s specialization was emitted with two parameters, a body of type
`bool`, and a declared return type of `bool -> bool`:

```c
static bool (*RestrictArity_mk_eq_test__bool(bool x, bool x1))(bool) {
  return (x && x1);
}
```

This is `Extract`'s `peel`, and the comment directly above it describes the
bug it had.  `peel` consumes one arrow per extra lambda binder the body
opened, and the arrows can be hidden behind an abbreviation -- which is why
the term-level `peel_typ` re-normalizes at every step.  Its `cty`-level
fallback did not: it called `head_ty` **once, on the way in**, and then
matched `TArrow` structurally.  `eq_test bool` unfolds to one arrow whose
codomain is `eq_test_for`, which is *another* abbreviation hiding the second
arrow.  So peeling two binders consumed the first arrow, landed on a name,
and stopped -- while both binders were emitted anyway.  The declared arity
exceeded the real one by exactly the number of abbreviation layers below the
first.

`peel` now unfolds at every step, like its term-level twin.  When it stops
early it returns the type as it was written rather than as it unfolds, since
the abbreviation is the better name.

This one deserves its own note on severity, because it is the kind that gets
through.  gcc 13 accepts the definition with `-Wint-conversion` and the
program prints the *correct* answer, because a `bool` round-trips through a
pointer on that ABI.  That is luck, not a property: it is a constraint
violation either way, and on gcc 14 `-Wincompatible-pointer-types` is an error
by default, so the same output is a hard failure on a newer toolchain.  A
backend that is right only on the compiler it was tested against is section
23's thesis again -- and note that our own `-Wall -Wextra -Werror` corpus
would have caught this had any test in it produced the shape.

### 26.3 The check does fire

The reporter observed that nothing covered the section 25 call-arity check
actually firing -- it caught 26.1's symptom in one program, and after the fix
that program compiles.  It is still reachable, and the case it exists for is a
partial application that eta-expansion cannot reach because there is no
declaration to give binders to:

```fstar
let use (a: bool) : bool = let k : bool -> bool = band a in k true
```

`tests/custard/CPartialCall.fst` pins it.  The message now says what is true
of both routes to it: a top-level partial application is expanded
automatically, so reaching this point means either a local one -- name it as a
top-level function taking every argument -- or a body too costly to
re-evaluate per call, which is 25.3.

### 26.4 What the two have in common

Both are the same mistake at different scales: **a fact about arity read off
the wrong representation**.  26.1 reads it off a binder list when the object
is a variable; 26.2 reads it off a structural `TArrow` match when the type is
a name.  Section 25 was a third instance -- reading it off a table that was
one rewrite out of date.  The general shape is that Custard has several
notions of "how many arguments", and they are only accidentally in agreement
unless something forces them to be; the call-arity check is that forcing
function, and it is worth more than the individual fixes.


## 27. A constant function compiled to mutable state

Round 21 of the EverParse report is mostly good news: both section 26 fixes
hold, a full regression over 12,109 CBOR inputs is byte-identical between the
C and the Rust paths, and the real CDDL combinator library now extracts and
runs given three `[@@@monomorphize]` attributes.  What is left is one finding,
and it is not a code-quality complaint.

### 27.1 The shape

```fstar
let id_fn (phi: (bool -> bool -> bool)) : (bool -> bool -> bool) = phi
let band (a: bool) (b: bool) : bool = a && b
let wrapped : bool -> bool -> bool = id_fn band
let use (a: bool) (b: bool) : bool = wrapped a b
```

`wrapped` used to come out as a `static` variable of function-pointer type,
declared empty and assigned inside `custard_init_globals`, with `use`
dereferencing it.  In EverParse the same shape arises from
`CDDL.Spec.EqTest.mk_eq_test`, whose whole body is `return phi;`.

### 27.2 Why this is a safety bug and not a slow path

Section 24 lists `custard_init_globals` as a *linking* obligation: call it
before anything else in the unit.  This turns it into a **memory-safety**
obligation.  `use` is a public entry point, `wrapped` is a null pointer until
the initializer runs, and so a caller who links the unit correctly but forgets
one call gets a jump through null rather than a wrong answer.  The definition
that earned this has no state in it: it is pure, total, and a compile-time
constant.

It is also a cost on the hot path -- an indirect call through memory where a
direct call to a known `static` function would do, which is precisely the call
an optimizer cannot inline.

### 27.3 Why the obvious fix is wrong

The blocker is *not* section 25.3's `cheap_expr`, which already admits this
body.  It is the arity bound in `eta_expand_decl`: the head `id_fn` has arity
one and is given one argument, so nothing is missing and no expansion is owed.

The tempting repair is to expand whenever the head is a known top-level
function whose arguments are cheap.  That is unsound as a *performance*
matter, and section 25.3 says why in passing without drawing the conclusion:
`cheap_expr` was only ever safe because it was applied to an **under**-applied
head, and an under-applied call allocates a closure and runs nothing.  Lift
that restriction and

```fstar
let table : int -> int = build_table 1000000
```

becomes `table x = build_table 1000000 x`, rebuilding the table on every call.
`build_table` is a known top-level function and `1000000` is cheap, so the
proposed rule fires and the program silently acquires a new asymptotic
complexity.  A miscompilation announces itself; this would not.

### 27.4 Forwarders

The repair Custard takes instead removes a call rather than moving one.  Call
a definition a **forwarder** when it is pure, non-recursive, and its body is
*exactly one of its own binders*.  Such a definition, fully applied, is the
identity on that argument, so

    f a1 ... an   -->   ai

whenever `f` is a forwarder returning its `i`th binder and the call is
saturated.  The other arguments are dropped, which is why they are required to
be pure -- ANF (§6 pass 1) has already made every operand pure, so the check
never fails in practice and is there to keep the rule honest if ANF ever
stops.

This cannot duplicate work, because the right-hand side is a subterm of the
left.  Where the general rule would have made `build_table` run per call, this
one deletes an indirection and nothing else.

`id_fn band` therefore reduces to `band`, leaving a definition whose body is a
name -- and the `EQual` case of `eta_expand_decl` already knows how to turn
that into a real function.  So `wrapped` becomes a `static` C function, the
call at the use site becomes direct, `id_fn` is unreachable and dies in DCE,
and `custard_init_globals` is empty and is not emitted at all.  The fix for
the safety bug and the fix for the hot path are the same fix.

The rule lives in `Simplify.reduce`, next to beta and iota, with its table
built at the start of the `reduce` pass.  Putting it there rather than in a
pass of its own matters: `reduce` runs bottom-up, so a call to a forwarder
whose argument is itself such a call collapses in one traversal, and `reduce`
runs well before `eta_expand`, which is what has to see the result.

### 27.5 What it cost the test suite

Four existing tests contained a forwarder incidentally and stopped testing
what they were written for once the rule deleted it -- `Implicits` (proof
binder erasure), `RetArity` (peeling abbreviations off a result type),
`WarnAny` (the `TAny` warning), `CVarArity` (§26.1's function-pointer
lowering).  Each was rewritten so that its subject function *uses* its
arguments instead of returning one, and each now says so in its header
comment.  That is the honest reading of four broken tests: the rule was doing
its job in four places where the test author had not thought about it.

`CVarArity` is the interesting one, because the shape it pins -- a global of
function-pointer type -- is still reachable and still has to be lowered that
way; §25.3 keeps it deliberately.  The forwarder rule narrows the set of
programs that get there; it does not empty it.

### 27.6 Still open

`custard_init_globals` remains a real obligation for programs that genuinely
have initialized global state, and section 24 should be read as saying that
skipping it is undefined behaviour and not merely a wrong answer.

`LamStruct` -- a lambda stored in a record field -- is still an honest 368
with no workaround, and is the shape a CDDL `bundle` uses.  The three
`[@@@monomorphize]` attributes CDDL needs would be inferred by M7.


## 28. A divergence the budget was for

[#4494] reports that the legacy extraction pipelines can be made to allocate
without bound and be OOM-killed, with no message naming anything.  The
question it raises for Custard is whether §3.6's step budget is the "broader
fix" that report says is still missing.  It is, and this section records the
measurement rather than the argument.

[#4494]: https://github.com/FStarLang/FStar/pull/4494

### 28.1 The shape

`FStar.Pervasives.false_elim` is defined as

```fstar
let rec false_elim #_ _ = false_elim ()
```

Since 1cb59d14cc, `FStar.Pervasives` is in `Dep.interfaces_with_inlining`, so
with `--cmi` -- the default -- that body is delta-unfoldable in every client.
Extraction normalizes *types* with delta, so a type computed by it

```fstar
let t (sq: squash False) : Type0 = false_elim ()
let f (sq: squash False) (x: t sq) : nat = 0
```

unfolds `false_elim () -> false_elim () -> ...` forever.  Nothing about this
is specific to `false_elim`: any recursive definition whose unfolding makes no
progress has it, and cross-module inlining exposes many more of them than it
used to.

### 28.2 What Custard does

Measured on this tree, on the report's own single-module reduction:

| pipeline | result |
| --- | --- |
| `--codegen OCaml` | `Fatal error: allocation failure during minor GC`, core dumped |
| `--codegen Custard`, `f` reachable | error 365 in well under a second |

The error names the term and the chain that asked for it:

```
* Error 365:
  - Custard exceeded --custard_norm_budget (10000000 reduction steps) while
    normalizing a binder's sort.
  - The term being normalized, before reduction, was: t sq
  - Reached through:
  -   TypeDiverge.f
```

Two things are doing the work, and they are worth keeping apart.

The budget is the one that matters, and it is not a lucky escape: §3.6 put it
there for exactly this failure mode, in the same words -- "not a wrong answer
or a rejection, but a compiler that never finishes and never says why".  What
is new is only that it now has an independent witness.  Note in particular
that `norm_bounded` covers *type* normalization and not just specialization
keys, which is where §3.6's original motivation lay; the report's case is a
binder's sort, and it is caught because the wrapper was applied uniformly
rather than at the one call site that motivated it.

The second is weaker but real: extraction is demand-driven from an entry point
(§3.2), so a definition nothing reaches is never normalized at all.  In the
report's reduction `f` is dead, and Custard extracts the module in 0.2 s
without noticing.  This is why `tests/custard/TypeDiverge.fst` has to name `f`
with `--custard_entry` to test anything -- and it is a real difference in
exposure, since the legacy pipeline extracts every definition in the module
whether or not the program uses it.  It is not a *fix*, and it should not be
offered as one: a program that genuinely calls into this territory gets there.

`TypeDiverge.fst` spells the recursive definition out rather than importing
`false_elim`, so that it goes on testing the hazard after #4494 marks
`false_elim` `irreducible`.  The shape is the hazard; the one name is not.

### 28.3 `false_elim` should have been an abort

The second half of the report's question is what `false_elim` becomes, and the
answer was: worse than it should be.

`Prims.magic` and `Prims.admit` have had a builtin rule since M2 mapping them
to `EAbort` at `TAny` -- they typecheck only because the caller has proved the
point unreachable, there is no value of the result type to produce, and `TAny`
lets the abort stand where a value of any type is wanted.  `false_elim` is the
same construct in a third spelling and had no rule, so Custard extracted its
*definition*:

```ocaml
let rec fStar_Pervasives_false_elim (u : unit) : 'a =
  (fStar_Pervasives_false_elim ())
```

That is bad in two different ways.  On OCaml it is an infinite loop where a
`failwith` belongs, so a program that reaches provably-unreachable code hangs
instead of saying so -- the same failure mode as §28.1, moved from compile
time to run time.  On C it was not emitted at all: the result type is a type
variable, so a hard 368, and with `--custard_monomorphize_types true` it
became a 368 about `Prims.int` -- an unrepresentable *return* type for a
function that never returns.

`Builtins.pervasives_rule` now gives it the same `EAbort`/`TAny` treatment as
`magic` and `admit`, so OCaml gets `failwith "FStar.Pervasives.false_elim"`
and C gets

```c
static uint32_t CFalseElim_g(void) {
  /* FStar.Pervasives.false_elim */
  abort();
}
```

where before there was no C output at all.  `tests/custard/CFalseElim.fst`.

One wrinkle worth recording, because it broke a test on the way in:
`FStar.Pervasives` is also a *realized* module, so the new branch in the rule
dispatcher has to fall through rather than shadow.  Claiming the namespace and
returning `None` for everything else silently cut `Mkdtuple3` and the rest of
the module off from `is_realized_module`, which `tests/custard/Realized.fst`
caught immediately.


## 29. Integer literals change representation underneath us

A master merge replaced `Const_int of string & option (signedness & width)`
with a *value* and the base it was written in, and split machine integers into
their own `Const_machine_int`.  Custard's own IR is unaffected -- `CInt` still
carries a string and an optional width -- so the whole change lands at the
boundary, in three places, and each one wants a different answer.

`constant_of_sconst` keeps the **source spelling**, via
`string_of_int_literal v b`: a literal written `0xFF` should come out `0xFF`
in the generated C.  This is exactly what the legacy ML extraction does with
the same two cases, so the two pipelines agree by construction.

`key_of_const` must do the opposite and use the **value**.  The base is not
part of what a literal means -- `FStarC.Const.eq_const` ignores it -- so a key
that kept it would let `f 16` and `f 0x10` specialize twice, producing two
identical definitions under two names.  This was not a live bug before, since
the old representation had no base to leak, but the new one hands us a way to
get it wrong and the fix is to spend the base on the way in.

`hint_of_term` is cosmetic and uses the value too, on the grounds that `0x10`
is a worse fragment of a generated name than `16`.

### 29.1 A measurement that quietly got weaker

`string_of_int_literal` canonicalizes hex to **lowercase with no leading
zeros**, so a source `0x1A` is now `0x1a` in the C and `0x00` is `0x0`.  That
is upstream's spelling and not Custard's to argue with; it is also invisible,
because nothing in any suite pins the case of a hex literal.

What it did break was `cbor-corpus/mutants.py`, whose `byte+1` family matched
`0x([0-9A-F]{2})`.  Ten literals stopped matching, so the harness generated
ten fewer mutants and reported

| | before | after the merge | after the fix |
| --- | --- | --- | --- |
| `CborBoundary` consts | 46 / 46 | 36 / 36 | 46 / 46 |
| `CborBoundarySlice` consts | 46 / 59 | 36 / 49 | 46 / 59 |

Every mutant that was killed before was still killed; the *denominator* moved.
A mutation score is a claim about a corpus, and a pattern that silently
matches less makes the claim weaker while leaving the number looking healthy
-- 36/36 reads better than 46/46 does.  This is §23.4's lesson in a second
form: there, a green run that compiled nothing; here, a ratio computed over a
shrinking population.  Both are answers to a question that stopped being
asked.

The pattern now accepts one or two digits in either case, and all four figures
are back to 46/46, 46/46, 48/49, 46/59.

### 29.2 Two unrelated bits of merge fallout

`no_auto_projectors` is now a deprecated no-op: F* declares projectors without
defining them unconditionally.  `AssumedProj.fsti` used the attribute to
*arrange* the shape it tests, so it now simply drops it -- the shape is the
default rather than something to ask for, which makes the test more general
and not less.

`false_elim` is `irreducible` as of #4494, and both §28 tests survive it
unchanged, which is what they were written for: `TypeDiverge` spells its own
recursion out rather than importing the name, and `CFalseElim` goes through a
builtin rule keyed on the lident, which no reducibility qualifier affects.


## 30. A function that returns a function pointer

Round 22 of the EverParse retest withdrew the framing of round 21.  A function
pointer stored in a record is not the problem, and never was: `ok_inline`
below, which builds a one-field record inline and calls through its field,
compiles and runs.  What blocks CDDL is two narrower things, and
`--custard_warn_any` is what separated them.

```fstar
noeq type fixedb = { fmeasure: U8.t -> SZ.t }
let mk_arg (x: U8.t) : fixedb = { fmeasure = measure_u8 }

fn use_arg (x: U8.t) returns n: SZ.t
{ let b = mk_arg x; b.fmeasure x }
```

`mk_arg` takes one argument.  Custard reported it as taking two, and so
diagnosed the saturated call in `use_arg` as a partial application:

```
Error 368: the partial application of BundleMWE.mk_arg has no C
representation.  It is applied to 1 of its 2 arguments.
```

The arity was not misread.  It was *created*, by Custard, one pass earlier.

### 30.1 Where the second argument came from

`fixedb` has a single field, so §5.2 collapses it to that field's type.  After
the collapse `mk_arg` has type `u8 -> (u8 -> usize)`, and §25's eta expansion
saw a definition whose result type is still an arrow -- exactly its trigger --
and gave it the trailing argument:

```
let BundleMWE.mk_arg (x: u8) (eta: u8) : usize = BundleMWE.measure_u8 eta
```

The rewrite is well typed and locally reasonable.  It is also wrong, for a
reason §25 did not consider: expansion changes the arity of a definition and
rewrites *only that definition*.  Every call site is left as it was.  That is
harmless when the callers were already asking for more than the definition
accepted -- which is the shape §25 exists for, and where the extra arguments
are already at the call sites waiting -- and a miscompilation when they were
not.  Here they were not.  `mk_arg x` was correct, complete, and had nothing
left to give.

There was never anything to fix.  A function returning a function pointer is
ordinary C, and with the expansion suppressed it is what comes out:

```c
static size_t (*PulseFnPtrRet_mk_arg(uint8_t x))(uint8_t) {
  return PulseFnPtrRet_measure_wide;
}
```

This is the fourth defect in the family §25 and §26 opened, and the first in
which the pass is not reading an arity off the wrong representation but
*imposing* one.  The bound that §26.1 added -- read a parameterless
definition's arity off its type -- is still right; what was missing is that
raising an arity is only sound if the callers can follow.

### 30.2 Only a use that cannot grow may pin a name

The fix is a second table, computed per round alongside `decl_arity`: the
fewest arguments any use of a name supplies.  A name used at `n` arguments may
not be expanded past `n`.  A bare `EQual` counts as a use at zero, so taking a
function's address pins it completely, and a name with no uses at all is
unconstrained.

The subtlety is which uses count, and getting it wrong fails `CEtaChain`
immediately.  That test contains

```fstar
let call_g_partial (a: bool) : (bool -> bool) = g a
```

which uses `g` at one argument -- but only for now.  `call_g_partial` is
itself about to be expanded, and when it is, that call becomes `g a eta`.
Counting it would pin `g` at one, `g` would then not be expanded, and the
chain §25 was written to resolve would stop one link in.

So a use pins a name only if this pass has no way to grow it.  Exactly one
kind can grow: the head call of an expandable definition's body, which is
where `eta_expand_decl` appends.  Every other use -- under a `let`, in an
argument position, as a bare address -- is final.  `mk_arg`'s single use sits
under a `let`, which is why it pins and `g`'s does not.

`tests/custard/pulse/PulseFnPtrRet.fst` holds all three shapes: a nullary
maker, a maker with an argument, and `pick`, a genuine §25 chain that must
still be expanded.  It checks its own answers and is run, so a function
pointer that goes to the wrong place is a nonzero exit rather than something
to be read out of the generated C.

### 30.3 The other half: a `Type0` field is an existential

The second bug in round 22 is not an arity defect and is not fixed.  §30.5
narrows it considerably -- most of what this section calls unsupported turned
out to be a stuck projection rather than an existential -- but the residue
below is real and is what remains.

```fstar
noeq type pbundle = {
  pimpl_type: Type0;
  pmeasure: pimpl_type -> SZ.t;
}
```

`pimpl_type` is a *field* of kind `Type0`, and `pmeasure`'s type depends on
it.  Erasure drops the type field, the record collapses to `pmeasure`, and the
sibling field's type is translated with `pimpl_type` still a bound variable
that has no representation -- so it becomes `any -> usize`, and 368 follows.
The *value* is recovered correctly; only its type is lost:

```
let b: any -> usize = BundleMWE.measure_u8 in b x
```

This is not the same problem wearing a different hat.  §6's type
monomorphization keys on the arguments of a type *constructor*; here the
argument arrives as a field value at each construction site, and `pbundle` is
an existential package rather than an instance of a parameterized type.
Compiling it means promoting the `Type0` field to a type parameter and
propagating the instantiation through every signature that mentions the
record -- which is inference, and which has no answer at all when one function
takes a `pbundle` at two different instantiations.  It is a feature at the
scale of §6, not a repair, and it is recorded here as the open item it is.

The narrow inline case above could be papered over -- the bound expression's
own type is precise, and preferring it over a `TAny`-infected ascription would
make `bug_a_inline` compile.  That is not worth doing.  It would fix the
reduced test and none of the real ones, since CDDL's bundles are returned
from functions and stored, and it would replace a clear 368 with a silent
reinterpretation in exactly the place §5.9 asks for a loud one.


### 30.4 Advice that cannot be followed

Error 364 tells the reader to mark the offending name `[@@monomorphize]` "in
the enclosing definition".  In the CDDL bundles that name is `ab_impl_type`,
which is a *field*, and the reporter did the obvious thing and wrote the
attribute on it.  It is a no-op: `Mono.classify` runs over the binders of a
function type, a constructor field never reaches it, and nothing else reads
the attribute either.  Same warning, same error, no acknowledgement -- which
is indistinguishable from having fixed nothing.

Two changes.  The attribute on a constructor field is now warning 371, which
says that it is read by nothing and why.  And 364 no longer gives advice it
cannot support: `st.defbinders` records the binders of the definition being
extracted, and when the name is not among them the message says there is
nowhere to write the attribute instead of naming a place that does not exist.

This is the same trap as rule 4's no-op on type binders, and §19.13's advice
that recommended a flag the reader had already set.  Advice that names an
action is read as an assertion that the action exists.

### 30.5 A field projection is not a type constructor

The `Type0` field of §30.3 is worse than it needs to be, and separating the
two halves took an MWE with CDDL's actual shape: a derivation over a grammar,
a bundle built by structural recursion over it, and combinators that build the
impl type with `&`, `option` and `either`.

The first finding is that specialization already does its half.  With the
derivation `[@@monomorphize]` the recursion unrolls -- the IR holds
`impl@Leaf`, `impl@Concat` -- and with the bundle arguments marked too, every
combinator is specialized per bundle *value*.  So at each construction site
the record really is concrete, and `b1.impl_type` is a projection out of a
known constructor application.

It was still `any`, for a reason that has nothing to do with existentials: a
projector is not a type constructor, so `ty_of_typ` fell through to
`ty_of_fv`, which has no answer for one.  `ty_of_typ` already has two cases
that reduce a stuck type -- a beta-redex in type position (§19.x) and an
abbreviation with an unrepresentable parameter (§18) -- and this is a third of
exactly the same kind.  Unfolding the projector and letting iota meet the
constructor gives the ground type.  The scrutinee has to unfold too, and by
delta rather than by name, because the record is as often a top-level
definition as a literal constructor application and iota cannot see through a
name.

The effect on the MWE is most of the way:

```
let concat_bundle__lam@Mkbundle
  (x: tuple2@tuple2_uint8_uint8_option_uint8) : usize
```

where before the same binder was `tuple2@any_any_option_any`, and before that
plain `any`.  The interior of every specialization is now ground.

What remains is one thing, and it is §30.3 in its exact form: the record's own
*declaration*.  `bundle` collapses to its surviving field, whose type is
`impl_type -> SZ.t` with `impl_type` still the type field, so the declaration
is `any -> usize` however concrete each use is.  Fixing that means emitting a
copy of the record type per ground value of its `Type0` fields -- §6 keyed on
a field rather than on a type argument.  That is a bounded amount of work now
rather than an open question, because the value it would key on is exactly
what §30.5 just made available.

This turned out not to be needed; §30.7 closes it another way.

`tests/custard/CTypeField.fst` is the part that works, isolated: a `Type0`
field projected in a type position, where the record's surviving fields do
*not* mention it, so no existential arises and the two specializations come
out over `uint8_t` and `uint32_t`.  It is compiled and run.


### 30.6 A reduction that may give up

Round 23 reduced the remaining half to a single line of difference.  A bundle
built by an `unfold` function extracts cleanly; the same bundle built by a
`let rec` does not.  An `unfold` builder is gone by extraction time, so it
never depended on any of this; a recursive one cannot be `unfold`, so
monomorphization emits specialized *definitions*, the bundle survives as a
value, and its `Type0` field has to be reached where it stands.

Reaching it needs `Zeta` in §30.5's step list, and `Zeta` is exactly what
makes a budget overrun possible: unfolding a recursive definition inside a
type need not terminate.  Adding it naively would convert programs that
compile today -- with an `any` in a place they never used -- into a hard error
365, which is a bad trade for a reduction whose whole purpose is to *recover*
precision.

So the reduction is allowed to give up.  `norm_optional` runs the normalizer
under the same budget as `norm_bounded` but returns `None` on
`Budget_exceeded` instead of raising, and the projector case reads `None` as
`TAny` -- the answer it would have produced had the case not existed.  The
distinction is worth stating generally: a normalization the *program's meaning*
depends on must fail loudly when it runs out of budget, and a normalization
that only sharpens a fallback must not.  §30.5's is the second kind, and it is
the first of that kind in the file.

### 30.7 Reading a declaration's type off its body

`Zeta` fixes the *uses*.  `use_rec`'s signature becomes `uint8_t
use_rec(uint8_t)`, its interior is ground, and the projection is gone.  It
does not fix the builder, and the error was always in the builder:

```
let RecTyField.mk_bundle_rec@AU8 : any = (0uy <: any)
```

The body knows the answer.  The declaration cannot: `bundle = { b_impl_type:
Type0; b_dflt: b_impl_type }` erases its type field and collapses to `b_dflt`
(§5.2), whose declared type is the field that just erased, so *every*
specialization of the builder is declared `any` however concrete it is.  This
is the §30.3 residue, and it turns out not to need §6 keyed on a field at all.

A declared `TAny` is not a claim that a value has no representation; it is
`Extract` reporting that it could not work one out.  Nothing is relying on it,
and anything else is an improvement.  So `Simplify.narrow_rets` reads the
result type back off the body: where a declaration's result type mentions
`TAny` anywhere and the body's does not, the body's wins.

Three things make it work rather than merely sound.

It runs after `records`.  That is the pass that turns the collapsed record
into its field's own type, so before it the body is no more ground than the
declaration.

It iterates.  A definition often returns nothing but a call to another one
whose type is being recovered in the same pass -- in `RecTyField` the chain is
`mk_bundle_rec@AU8`, then `@ANode`, then the lambda that returns it, then
`use_rec`; in the CDDL bundles it is as deep as the grammar derivation.  Each
round can only replace a `TAny` by a ground type, so it converges; the bound
of 20 is there so that a malformed program cannot hang.

It rewrites only the declarations.  `coerce_prog` re-derives an `EQual`'s type
from the signature rather than from the node it sits in, so narrowing a
signature is enough for every use to follow, and the coercions that stood
between them disappear on their own because the two sides now agree.  This is
why the fix belongs here and not in `Extract`, where an earlier attempt failed
for the opposite reason: at extraction time the collapse has not happened yet
and the body's type is just as `any` as the declaration's.

`tests/custard/RecTyField.fst` carries both halves, the `unfold` control and
the recursive case, over two instantiations each; it is compiled and run, and
generates no `any` at all.

### 30.8 The same field, spelled three ways

Round 24 found that §30.5 and §30.7 fixed the *spelling* CDDL does not use.
CDDL never writes `b.b_impl_type`.  It destructures with a `match`
(`CDDL.Pulse.Bundle.MapGroup`), and where it does not, it goes through an
accessor with a `Pure ... ensures fun t -> t == b.b_impl_type` guard
(`CDDL.Pulse.Bundle.Base`).  Both hide the projection, and the three forms
failed in three different ways:

| how the field is written | before | why |
| --- | --- | --- |
| `(mk_bundle a).b_impl_type` | works | §30.5 reduces the projector |
| `match mk_bundle a with Mkbundle it d -> ...` | Error 364 | the field is now a *variable* |
| `get_impl_type (mk_bundle a)` | Error 368 | the bundle reaches a runtime binder |

Nothing about the program differs between the three.  The same value is
available at the same moment with the same annotations; only the syntax
differs, and syntax is not a reason to support one and reject the others.

**The `match`.**  A constructor that stores a type -- `Mkbundle : (b_impl_type:
Type0) -> (b_dflt: b_impl_type) -> bundle` -- binds that type to a variable
when it is matched, and a variable standing for a type is precisely what error
364 reports.  Such a match has to fire at specialization time or never, so
`specialize` now reduces it: it scans the body for a match on a type-storing
constructor, collects the head names of those scrutinees, and normalizes with
`Zeta` and delta *for those names only*.

Every part of that narrowness is load-bearing.  §6 excludes `Zeta` for reasons
that have not stopped being true, and unfolding every reachable recursive
definition would be a different compiler.  Here it is on for a handful of
named builders, and only when the shape that needs it is present.  The
reduction is also allowed to fail: on a budget overrun the ordinary
normalization runs instead, and the program gets whatever diagnostic it would
have got before rather than a fresh error 365 -- the §30.6 rule again.

The first version of the trigger was wrong in an instructive way.  It asked
whether the matched constructor binds a type *anywhere*, which is true of
`Some : (a:Type) -> a -> option a`, so every `match` on an `option` fired it
and `tests/custard/Magic.fst` lost its dictionary specialization.  What matters
is a type a constructor **stores**, which is its arguments past the inductive's
own parameters.  `Mono.ctor_stores_type` is that check, and both this and rule
4b below use it.

**The accessor.**  `get_impl_type (mk_bundle a)` in type position is an
ordinary function applied to arguments, not a type constructor, so `ty_of_fv`
had no answer.  §30.5's reduction now runs as a *fallback* there -- only once
`ty_of_fv` has returned `TAny`, so a type that does have a name is unaffected
-- which makes the accessor and the projection behave alike, as they should.

### 30.9 Rule 4b: a type-carrying value has no runtime representation

The accessor's other half is its argument.  `get_dflt (b: bundle)` takes the
bundle as a runtime parameter, and a bundle has no runtime representation to
take: its own contents decide what it is.  The declared type collapses to
`any`, and 368 follows.

This is not a case for `any`; it is a case that cannot exist.  So rule 4b joins
§3.1: **a binder whose type is an inductive one of whose constructors stores a
type is `Mono`**, whether or not anyone wrote the attribute.  The alternative
is not a slower program but no program, which is what separates this from the
inference rules §3.1 leaves opt-in.

The inductive's own parameters are again excluded, and again for `Cons : (a:
Type) -> a -> list a -> list a`: `list int` is an ordinary runtime value.

Rule 4b changes one existing test's verdict.  `tests/custard/FieldAttr.fst`
pinned warning 371 with a 368 behind it; the 368 is gone, because the binder
is now `Mono`, so the warning is promoted with `--warn_error @371` and stands
on its own.  That is the right outcome for it: the attribute is still read by
nothing, which is all it ever claimed.

**And the local binding.**  With all three forms extracting, one leak was
left: `let a = by_acc ... in` still carried `any`, because the annotation is a
copy of the callee's declared result type taken *before* `narrow_rets`
recovered it.  `coerce_prog` already infers the better type in order to bind
the variable; it now writes it back into the annotation as well.  Without
that, a `void *` local was the one place the recovered type was still thrown
away.

`tests/custard/RecTyAcc.fst` carries all three spellings over two
instantiations, checks its own answer, and is compiled and run.

### 30.10 Opt-in compile-time evaluation

Custard does not evaluate closed terms.  A program that computes something at
run time is meant to compute it at run time, and an extractor that reduced
whenever it could would make every definition's body part of every caller --
in C as much as in OCaml, and for the same reason: the output would stop
resembling the input.  §3.5's normalization exists to make *types* ground, not
to run the program.

But some definitions exist only to produce a constant, and compiling them is
the wrong answer rather than a slower one.  EverParse has the example.
`CDDL.Pulse.AST.Literal.string_length` is

```
let string_length (x: string) : nat =
  List.Tot.length (String.list_of_string x)
```

and every call in the corpus applies it to a literal.  Compiling it asks C for
a `list char`, which C does not have -- error 368, reporting a list the author
never wrote in a definition they did not know was involved.

So the decision is handed to the author, one definition at a time:
`[@@custard_compile_time]` on a definition means *every application of this is
evaluated during extraction*.  `expr_of_term` checks the head of each
application it meets against the attribute, and, when it matches, normalizes
the whole application with everything on -- delta to `delta_constant`, `Zeta`
so a recursive definition over a literal runs, `SafePrimops` so the primitives
underneath it fold -- and continues with the result.

**The promise is checked, and checked before it is used.**  The natural test
is on the reduct: if the head is still the marked name, nothing was computed.
That test does not work.  Unfolding removes the head whether or not anything
was computed -- `string_length s` for an unknown `s` reduces to the `match` in
its body, which is headed by nothing at all -- so the check would pass exactly
the case it exists to catch, and the caller would be told about a `list char`
after all.

What decides the question is whether the arguments are known, and that is
visible before reducing: the application's free names.  An application with
any is error 372, naming the definition and the variables that made it
impossible.  An application that is closed and *still* stuck -- because a
definition it needs is abstract in the interface it was loaded through -- is
the same error with the other explanation.  Neither falls back to compiling
the definition, which is the whole point: falling back would be the worse
behaviour precisely where the attribute is useful.

A definition marked this way is free to have a type C could not compile, since
none of it is compiled.  That also says where to put the attribute: on the
outermost definition whose result *is* representable.
`tests/custard/CompileTime.fst` marks a wrapper returning a `UInt32.t` rather
than `string_length` itself, because an unbounded `nat` has no C
representation either; the `list char` and the `nat` both disappear, and the C
reads `uint32_t len = 5U`.  Its companion `CompileTimeBad.fst` pins the 372.

This is deliberately not an inference.  Custard could notice that an
application happens to be closed and evaluate it, but "happens to be closed"
is not a property an author controls, and a definition that silently stops
existing when its last non-literal caller is deleted is worse than one that
never existed.  The attribute is a statement of intent, and the error is what
makes it one.

### 30.11 Rule 4c: a binder a compile-time application needs

§30.10 makes the evaluation opt-in but says nothing about how the argument
comes to be a constant, and in EverParse it does not, by itself.
`CDDL.Pulse.AST.Literal.impl_literal` destructures a literal and hands the
string it finds to the marked function:

```
let impl_literal (l: literal { wf l }) =
  match l with
  | LTextString s -> string_len64 s
  | ...
```

`s` is a pattern variable, so the application depends on a runtime name and
error 372 fires.  Writing `[@@@monomorphize]` on `l` fixes it -- and then the
same error reappears at `impl_literal`'s caller, and at its caller.  That is
the annotation treadmill rule 4b exists to end.

Rule 4b does not reach this, and the reason is worth stating rather than
patching around.  It is keyed on a constructor that stores a *type*, and its
justification is that such a value has no runtime representation at all --
"the alternative is not a slower program but no program".  `LTextString`
stores a `string`, which has a perfectly good runtime representation.  What
makes it compile-time here is not the value's nature but the use it is put
to.

So rule 4c is a *demand*, read off the body rather than off the type: **a
binder that an application of a `custard_compile_time` definition depends on
is `Mono`**.  Two sources, both over-approximations, and deliberately in that
direction -- a demand met by a binder that did not need it costs one
specialization, one that is missed costs the extraction:

- the free names of a marked application, since they are exactly what stops
  it from reducing;
- if a marked application occurs inside a *branch*, the scrutinee's names,
  because knowing the argument means first knowing which branch is taken.

The second is also why the branch is not opened: a pattern variable is a de
Bruijn index there and has no name to collect, and the scrutinee is what can
be specialized on anyway.

**The demand is a list of positions, not of names.**  `classify` opens the
declaration's arrow and the body opens the lambda, so the same parameter is
two different `bv`s and matching on identity silently never fires -- which is
exactly what the first attempt did.  `compile_time_demanded` therefore opens
the lambda itself and reports indices, and `classify_demand` seeds them
*before* rule 5's fixpoint, so the demand propagates to whatever the demanded
binder's type mentions, and §3.1 rule 5 at the call sites carries it up the
chain.  That last part is what keeps this from being one annotation per level.

`tests/custard/LitStr.fst` carries the shape with no annotation anywhere, over
two string instantiations and one that takes the other branch.

The demand has to be *rooted* somewhere.  Rule 4c makes `impl_lit`'s binder
`Mono`; what makes that binder a literal is that some caller passed one, and
§3.1 rule 5 carries the requirement up from there.  Extract `impl_lit` itself
as an entry point -- `--custard_entry_module`, or a `--custard_entry` naming
it -- and there is no caller: its parameter is then a genuine runtime
parameter of the program being compiled, and error 372 is the right answer,
not a regression.  Entry points are the boundary at which a value stops being
a compile-time constant, which is the same reason §4.4 asks for them.

### 30.12 Three per-term-size costs

Round 31 profiled the extraction of a CDDL entry point by sampling stacks
under `gdb`, and the result was three distinct hot spots rather than one.  The
reconciling fact is that none of them is about *how many* specializations
there are -- 643 in total, at most 8 per definition -- and all three are per
*size* of the terms involved.

**A budget that did not bound anything.**  Two samples ten minutes apart
landed in the same place: 249 consecutive `Syntax.VisitM` frames under a
single `closure_as_term`.  `closure_as_term` erases universes by
`Visit.visit_term_univs`, which is a full deep traversal and fresh copy of the
whole term, and Custard sets `EraseUniverses`, so every rebuild of an
irreducible term pays it.  `charge_step`'s comment claimed the count was
"proportional to the work actually done" because it is charged once per `norm`
call.  That is false exactly here: one step costs one unit of budget and does
O(size-of-term) work, allocating a copy.  It explains every negative control
in rounds 30 and 31 -- budget 10 M, budget 1 G, `--custard_fuel 3000`, none of
which bounded the run, because from the budget's point of view nothing was
happening.  `_erase_universes` now charges per node.  A budget that does not
account for the dominant cost is not a smaller budget, it is not a budget.

**An uncached lookup on the hot path.**  `Env.disc_proj_info` does four
`lookup_qname`s and is called on every attempted projector or discriminator
reduction.  A program that is nothing but nested matches on projected fields
-- CDDL is exactly that -- spends a measurable fraction of extraction there.
The answer depends only on the name, and a name is never bound to two
declarations in one run, so `Normalize` memoizes it.

**Quadratic key rendering.**  `key_of_term` built a key with left-nested `^`,
which copies the prefix again at every node; keys for a deep grammar
derivation are megabytes long, and one is built per `request`.  The renderer
now appends into an accumulator that is concatenated once.  Nothing about
*what* is rendered changed, and it must not: §12.3's keys are compared as
strings, so a key that rendered differently would silently split or merge
specializations.

**And the profile has to survive the failure.**  `Universal` reports profiling
counters only after a file type-checks, so an extraction that raises reported
nothing -- and a run that fails is precisely the one worth profiling.  Round
31 could not get a breakdown out of any CDDL entry for that reason, and had to
use `gdb`.  `Driver.run` now reports on the way out whichever way it leaves.

### 30.13 A local that captures a top-level name

Found by running `make custard` rather than by a report, and worth recording
because the source that triggers it reads perfectly:

```
val mantissa (r : real) : int
val try_mk (mantissa exponent : int) : option real
```

`try_mk`'s parameters shadow the projections it then calls.  F* has no
difficulty with that -- the two live in different namespaces as far as the
type-checker is concerned -- but the emitted OCaml refers to a top-level value
of the same file *unqualified*, because inside `Foo` there is no way to write
`Foo.bar`.  So the local captures it, and the generated code either fails to
compile or, worse, compiles against the wrong binding.

The locals are renamed rather than the references qualified: a local's name
carries no meaning outside its definition, and a top-level name is what a
hand-written realization may be written against.  `reserve_top` collects the
file's top-level value names before it is printed -- *with `current_module`
already set*, since whether a declaration is spelled with a qualifier is
exactly the question -- and `ocaml_local` appends an underscore on a
collision.

Only value locals go through `ocaml_local`.  Record fields and type variables
keep `ocaml_var`, because a field's spelling has to match its type's
declaration, and that declaration may be a hand-written realization this run
does not get to rename.

The same run turned up two missing roots of §4.4's other kind.  `src/ml`'s
menhir grammars are hand-written OCaml, so nothing Custard can see reaches
what they call: `FStarC.Real.of_string` and `FStarC.Const.parse_int_literal`
are called from semantic actions, and `FStarC.Real.real` is an abbreviation
mentioned only there, which is unfolded rather than emitted unless it is
named.  All three join `entrypoints.txt`.  This is the documented failure mode
of a whole-program extractor with hand-written edges, and the only defence is
that the build catches it.

### 30.14 A parameter nothing observable depends on

Round 32 turned the §30.12 hang into an error, and the error named a term.
Extracting one CDDL entry point failed at 60 s on a type signature that was
9,012,230 bytes *before* reduction, reached through the simplest type CDDL
has: `bool`.  What it is made of is the point.  6995 occurrences of
`FStar.Ghost.reveal`, 4668 of the refinement on `cbor`, 2505 of
`FStar.Ghost.E`, 990 of `serializable` -- and in the signature it belongs to,
`impl_serialize`'s specification argument `s` occurs exactly once, inside a
`pure (...)` in a postcondition.  The compiled signature is three names:
`impl_tgt`, `S.slice U8.t`, `SZ.t`.  Not one byte of the 9 MB can reach the
output.

So the answer is not to reduce it faster.  It is not to ask for it.

`s` is `Mono`, and what `Mono` costs is not a parameter -- a `Mono` argument
is never passed at run time -- but a *specialization*: the argument is
normalized, rendered into a key (§12.3), compared against every other key, and
the definition is copied once per distinct one.  Rule 8 says a `Mono` binder
that nothing observable depends on is `Dropped` instead.

"Observable" is `Mono.observable`, a view of a type that keeps only what can
reach the emitted code: refinements replaced by the type they refine, and a
computation replaced by its result.  Those are the two places a specification
hides in a signature.  A refinement is a proposition and Custard compiles
`x:t{p}` as `t`.  A computation's pre- and postconditions are slprops, and
Pulse writes the interesting half of a signature there -- which is where the
9 MB was.  The view descends through arrows and refinements and leaves
everything else whole, so a name occurring somewhere it does not understand is
reported as occurring: it over-approximates towards keeping the binder.

Three things had to be got right, and each was got wrong first.

The **body** test is what makes the rule sound.  A parameter absent from a
signature can still be read at run time -- `if n = 0 then ...` mentions `n`
nowhere in the type -- and deleting one of those is §18.1's miscompilation
reached by a new path.  So a binder is dead only if it is absent from the body
*and* from the observable view of the rest of the signature.

The body has to be the body that is **compiled**.  `[@@extract_as]` replaces
one with the other, and the two need not mention the same parameters:
`tests/custard/Anf.fst`'s `tick` has the specification `fun s n -> n` and an
implementation that prints `s`.  Reading liveness off the specification
deleted the string, and the first run of the suite printed nothing.  The
classification site now applies `fixup_extract_as` before it looks.

The type can have **more binders than the lambda**.  A projector for `class
monad` is written as four abstractions over an arrow of six; the remaining two
are consumed inside the `match`.  Positions past the lambda's arity have no
binder in the body to ask about, and reading that as "absent" deleted
`mbind`'s first argument, which the OCaml compiler then caught.  Those
positions are live by construction.

And the rule is confined to `Mono` binders, which is what makes it free.
Turning a `Mono` binder into `Dropped` removes a compile-time key and changes
no signature, because a `Mono` argument was never passed.  The same move on a
`Poly` binder deletes a parameter callers still pass:
`tests/custard/RetArity.fst`'s `f` takes a `frame` and a `post` that are
unread and unmentioned, and they are part of its ABI regardless.

`tests/custard/DeadMono.fst` is the shape, reduced from round 32's own
measurement.  Its `Mono` argument is a computed list nobody looks at, and it
extracts under `--custard_norm_budget 100000` -- four orders of magnitude
below what normalizing the argument would take.  On the unreduced measurement
the cost was linear in the argument and split three ways, all of it
specialization: 517 ms in `norm`, 355 ms in `split_mono_args`, 302 ms in
`key`, for an argument of 25600 elements whose contribution to the output was
`return u;`.  With rule 8 the whole extraction is flat at 0.55 s.

§30.12's change of accounting also changed what a budget *is*: a step is now a
node of work rather than a reduction, so the same program needs a larger
number, and CDDL needs `--custard_norm_budget 100000000`.  The default stays
at 10^7 all the same, and the reason is worth recording, because the obvious
move is to raise it.  Raising it to 10^8 makes `tests/custard/TypeDiverge.fst`
overflow the stack instead of reporting error 365.  The budget is not a
performance knob -- it is what turns a nonterminating reduction into a
diagnosable error, and it only does that if it fires before the normalizer's
own recursion runs out of stack.  A project that needs more can ask for more,
in the one place that knows it does.

### 30.15 A name that doubles at every level

Round 33 retracted round 32's central number -- the term Custard choked on is
270 bytes, not 9 MB; the 9 MB was the "reached through" chain, and the ghost
counts were counts over that chain.  Which relocates the problem: the chain's
frames are specialization *instantiations*, so what is 8 MB is a **name**.
The frame in question spells out 421 nested `Mkbundle_env`, because CDDL
builds its environment by extending the previous one and the n-th extension's
argument contains all n-1 before it.

Reduced, that is 25 lines: a record whose type embeds the previous one, so
that each instantiation's name must spell out the accumulation.
`tests/custard/NameWidth.fst` is that file.  It does not fail -- it extracts
correctly at every depth -- it just costs, and what it cost was worth reading:

| depth | 4 | 6 | 8 | 10 | 12 |
| --- | --- | --- | --- | --- | --- |
| before | 0.33 s | 0.43 s | 1.26 s | 11.4 s | 159 s |
| after | 0.61 s | 0.77 s | 1.42 s | 4.09 s | 14.9 s |
| C bytes before | 8,785 | 25,686 | 85,595 | 317,540 | 1,237,635 |
| C bytes after | 6,976 | 11,032 | 15,088 | 19,188 | 23,318 |

The emitted C shrinks by 53× at depth 12 and stops doubling, because what was
doubling was the identifiers.  The longest one goes from **57,361 characters
to 82**.

Three separate faults, and the interesting part is that none of them is the
specialization machinery.  A profile put 96% of the run in `driver` exclusive
-- outside every counter -- at 57 specializations.

**`Monomorphize.hint_of_cty` was unbounded.**  It renders a type
structurally, with no depth limit and no width limit, and `TApp (n, [])`
renders through `n.spec` -- so an instantiation's name is built from the names
of the instantiations it is made of, and a type that nests doubles the name
per level.  It is now bounded in depth (4) and the assembled hint is clipped
to `hint_width` (48).  Truncating can only make two hints collide, and
`request`'s `pick` already resolves a collision by numbering, so nothing is
lost but spelling.  `Extract.fit`, the corresponding renderer for *terms*, had
the same hole for a different reason -- it kept the first component "whatever
its length", to avoid a hint of nothing -- and now truncates it instead.

**`FStarC_String.list_of_string` was quadratic.**  It was
`BatList.init (BatUTF8.length s) (fun i -> BatUChar.code (BatUTF8.get s i))`,
and `BatUTF8.get` walks from the start of the string, so indexing in a loop is
O(n²).  It folds now.  `string_of_list` had the mirror image of the same bug
and uses a buffer.  This is not Custard-specific -- it is on the path of
anything in the compiler that takes a string apart -- but Custard is what made
strings long enough for it to matter.

**`PrintC.sanitize` called it three times**, twice only to look at the first
character.  One pass now, and the first character is the one it already has.
`sanitize` runs on every name Custard prints, so 57,361² × 3 × 48 was the
153 seconds.

The width bound is the fix that matters, and the reason to prefer it over
making long names cheap is C99: an internal identifier is guaranteed
distinguishable only to 63 characters and an external one to 31.  A 57 KB
identifier is outside what any standard promises, whatever `gcc -Wall -Wextra`
accepts in silence.

What is left at depth 12 is 14.9 s in `ty` and `must_erase`, 283,807 calls
each, and that is the reproducer's own exponential: the F\* type at depth 12
is a 4096-leaf tuple tree.  Nothing is being recomputed that should not be.

### 30.16 An eta-reduction with nowhere to put the argument back

Also round 33, reported in passing.  `let consume (i: sig_t s) (u: U32.t) =
i u` -- where `sig_t` is an abbreviation that unfolds to an arrow -- reached
the C backend as Error 368, an over-application: `consume` takes 1 argument
and is applied to 2.

Eta-reduction (§25) shortened it to `fun i -> i`, correctly: the arrow it
dropped moves into the result type, and OCaml is perfectly happy to be handed
a function.  Eta-*expansion* is the pass that puts the argument back for C,
and it did not fire, because it reads how many arguments are still owed off
the **head of the body** -- and this body has no head.  It is a bare
parameter.  `head = None` meant `missing = 0`.

There is no callee arity to read here, but there are call sites, and the only
reason to expand a headless body at all is that one of them supplies more
arguments than the definition accepts -- which is exactly the condition the C
backend rejects.  So the demand is read off `use_arity` instead, bounded by
`arrow_arity` of the result type as every other case is, and it is zero when
no caller asks.  That keeps the pass from growing definitions nobody
over-applies.

`tests/custard/EtaVar.fst`, which emits
`EtaVar_consume(uint32_t (*i)(uint32_t), uint32_t eta)` and runs.

### 30.17 A value that is small only because it is shared

Round 34.  `CDDLTest.Test.bundle_signoutputargs` still fails, and the
measurements finally say what it is failing at.  It is not divergence.  Given
ten times the budget it runs ten times as long, allocates linearly up to 59
GB, and reports a byte-identical error with every profile counter unchanged.
The extra 900 million steps went into a single `norm` call that was making no
progress -- it was copying.

The shape is a record built from its predecessor:

```
let { b_typ = _; ...; b_parser = b_parser; b_serializer = b_serializer } =
  bundle_signoutputargs' in
Mkbundle ... (fun c -> ... b_parser c ...) (fun c out -> b_serializer ...)
```

one binding, five uses.  As written it is linear in the depth of the chain.
Its normal form is not: the `let` is a single-branch match, iota fires by
substituting the scrutinee's fields into the body, and the body mentions them
five times.  Every level multiplies.

That is a fact about the term, not about the reduction strategy, and it is
the answer to the question §12.3 leaves open.  A specialization key is a
normal form.  Producing one substitutes the sharing away.  So **a value that
is only small when shared cannot be specialized by value** -- not because
reducing it fails to terminate, but because the thing it reduces *to* is the
size the sharing was hiding.  No budget helps, because the budget is not the
problem.

The reduced form of this is 25 lines, `tests/custard/LetShare.fst`: a
three-field record of functions, an `ext` that takes it apart and uses each
field twice, and a chain of twelve.  At the default budget its normal form is
587 KB of OCaml and grows by a factor of two per link.

#### What a key is for

A key exists to *tell specializations apart*.  Two arguments that key
differently are compiled twice, which costs code and nothing else.  Two that
key the same are compiled once -- and that is the only direction that can be
wrong.  Canonicalizing further only ever merges; it never makes an answer
correct that was not.

So exhausting the budget while computing a key does not have to be an error.
It can fall back, as long as the fallback still distinguishes.  Two fallbacks
are already available and each is a form the argument really has:

1. the weak head normal form -- which §3.7 already computes, because it is
   what gets substituted into the specialized body;
2. the argument as written.

Both are keyed by the same `key_of_term`, which renders every node kind, so
neither needs the term to be in any particular form.  The second is sound for
the reason that matters here: *substituting a name preserves exactly the
sharing that reducing it would have destroyed*.  A name is a perfectly good
key, and a specialization identified by a name is compiled once per name.

`split_mono_args` now tries all three in order.  Both reductions run under
`norm_optional` rather than `norm_bounded`, so neither can fail the compile;
when the full one runs out, warning 373 says so, names the definition and the
binder, and says which form took its place.  The warning is worth having
because the alternative reading -- that Custard silently stopped
canonicalizing -- would be a surprise.

The cost is real and stated: a value written two ways may now be specialized
twice, where full reduction would have found them equal.  That is code size,
not a wrong answer.

#### What this gives up

Error 365 at a `Mono` argument is gone, and `tests/custard/NormBudget.fst`
now records a warning instead.  That test's argument is `spin 0`, where `spin`
is admitted total and unfolds forever; it used to be the demonstration that
§3.6's budget turns a hang into a diagnostic.

Giving it up is the right trade, because the two cases are not
distinguishable and the error was claiming they were.  Termination is
undecidable, and the obvious proxy -- "is a recursive definition reachable
from this argument?" -- was tried and is useless: `FStar.UInt32.add_mod`
reaches `Prims.pow2`, so `LetShare`'s twelve-link chain answers yes just as
`spin 0` does.  Nothing cheap separates a reduction that will not stop from
one that will not fit.

What Custard can do instead of guessing is *decline to reduce*, and that
turns out to be well defined for both.  `spin 0` is keyed and substituted as
written, `spin` is extracted as the recursive function it is, and the program
diverges when it is run -- which is what the F* program says.  The compiler
does not hang, which was the whole point of §3.6, and warning 373 still names
the definition and the term.

The budget itself is untouched everywhere else, and the case that really
cannot fall back still errors: a *type* computed by a divergent definition
has no as-written form a backend can use, so `tests/custard/TypeDiverge.fst`
-- the reproduction of PR #4494 -- is still error 365, from the type
normalization site.  So is `MonoFuel`, from §3.6's fuel.

#### What it buys

`LetShare` at a chain of 40 goes from Error 365 to 3.5 KB of OCaml, flat in
time, and what it emits is the source structure back:

```
let letShare_b40 : letShare_bnd = (letShare_ext letShare_b39)
let letShare_use__b40 (x : FStar_UInt32.t) : FStar_UInt32.t =
  ((letShare_b40).p x)
```

The specialization is keyed on the name `b40` and projects out of the shared
value -- which is the compilation an ML backend would have produced anyway,
and the one the sharing was there to make possible.

The test pins the part that could go wrong.  It runs, and the number it
prints is the number the 587 KB exponential form prints.  A fallback key that
distinguished too little would not merely be slower; it would print
something else.

#### What it does not fix

C is a separate matter.  `b40` is a record of closures, and the C backend has
no closures (§8.5), so `LetShare` is an OCaml test.  The CDDL bundles are
closures too, which is why the four CDDL entry points still report Error 368
on `b_parser`/`b_serializer` residuals: that is the `any` problem of §30.9,
untouched by this, and it is what §12.3's "specialize by value" was trying to
avoid in the first place.  This round says the avoidance has a hard limit,
and now says so with a diagnostic instead of a hang.

## 31 Honouring what the program already says

Round 35 is three reports with one shape between them.  EverParse has already
written down, by hand, which definitions must unfold and which must not --
`normalize_for_extraction` on every generated definition, `sem_attr`/
`base_attr` on the AST interpreter, a `delta_only` whitelist naming
`List.Tot.length` and `FStar.String.strlen` outright -- and Custard was
ignoring all of it and trying to rediscover the same set from §3.1's rules 4b
and 4c.

It should not.  Where the program says what it wants, that is the answer;
inference exists for where it does not.

### 31.1 `normalize_for_extraction`

`[@@normalize_for_extraction steps]` means: reduce this definition with
exactly these steps before compiling it.  The ML pipeline honours it in
`FStarC.Extraction.ML.Modul.extract_sig_let`, and that is why the krml
backend never meets EverParse's `validate_typ'` at all -- F\* has already
unfolded it against the concrete AST by the time extraction starts.  The
prebuilt `CDDLExtractionTest.c` contains no `validate_typ`, no `list` and no
`char`; karamel is not inlining an interpreter, it never sees one.

Custard has its own front end, so it met `validate_typ'` as written and,
correctly, reported that a `list char` has no C representation.  The 368 was
downstream of a missing pre-pass.

`Extract.fixup_normalize_for_extraction` is that pre-pass, applied wherever a
definition's sigelt is fetched, next to `fixup_extract_as`:

- the steps are themselves normalized first, exactly as the ML pipeline does,
  so a program may write `normalize_for_extraction (nbe :: T.steps)` rather
  than a literal list at every use;
- `Cfg.translate_norm_steps` turns them into normalizer steps, and an
  ill-formed attribute is a warning and a no-op, not a failure;
- the environment sets `erase_erasable_args`, which is what makes the
  reduction affordable -- a proof argument is dropped rather than reduced;
- `normalize_for_extraction_type` additionally normalizes the type;
- the reduction runs under `norm_bounded`, so §3.6's budget still applies.  A
  definition the programmer has explicitly asked to unfold is the one place
  where exhausting the budget really is an error and not a size problem: the
  request was specific, and the answer is to narrow the steps or raise the
  budget.

It is cached by lid.  `extract_lid` runs once per specialization, and the
attribute exists precisely because the reduction is expensive; without the
cache a definition with twenty specializations would pay for it twenty times.

`tests/custard/NormForExtraction.fst` is the CDDL shape in miniature: a
recursive interpreter over an AST applied to a closed constant, with a
whitelist that names the interpreter and the constant but deliberately *not*
`step`.  The test asserts both halves -- the `ast` datatype and both
`eval` functions are gone, and `step` survives as a call -- because a pass
that reduced too much would pass a test that only checked the first.

#### Why not infer it

The reporter tried the alternative, thoroughly: 34 `[@@@monomorphize]`
annotations across three EverParse files, which got two of the four CDDL
entry points to clean C with *no* pre-pass, and faster -- `uint` went from
141 s and an error to 13 s and 70 KB.  Specializing turns out to be cheaper
than normalizing, because the stock failures were spending their time
building giant normal forms for keys that specialization never needs.

That is a real result and it says the two routes are close to
interchangeable.  Both are honoured now, and neither is inferred.  The
argument for reading the attribute as well is that the delta set is
*per-use*, not per-definition: EverParse's own `steps` unfolds
`Mkbundle_env?.b_e_v`, `bundle_steps` excludes `Mkbundle?.b_parser`, and
`bundle_get_rel_steps` includes it.  No single global rule is right for all
three, and nothing Custard could infer would arrive at a set that
deliberately disagrees with itself.  The attribute is where that disagreement
is already written down.

### 31.2 Error 368 gets a chain

Errors 364, 365 and 373 print "Reached through", because extraction is
demand-driven and the chain is the demand.  Error 368 printed nothing but a
declaration name, and twice in a row that is what stopped the reporter:

```
* Error 368:
  - Custard: the abstract type Prims.int has no C representation, in
    Prims.op_Less.
```

`Prims.op_Less` is used everywhere in the CDDL sources, appears nowhere in
the output, and is absent from `--custard_dump_specializations`.  There is
nothing to act on.

The C backend has no request chain -- it runs after extraction, over the
whole program -- but it has the call graph, and reachability from a root is
the same information from the other end.  `PrintC.record_parents` walks
breadth-first from the roots recording who first reached each declaration, so
walking back up gives a shortest chain; a constructor resolves to its own
type, as `Simplify.dce` already does.  Both `reject` and `reject_ir` append
it.

### 31.3 What "did not reach" actually meant

The other half of the same complaint.  For `FStar.List.Tot.Base.isEmpty@char`
the old message read:

> `--custard_monomorphize_types` is already set, so this type is one the
> monomorphization pass did not reach.  That is a Custard bug, please report
> it.

It is not a bug and the pass did reach it.  `FStar.List.Tot.Base` is realized
by hand in OCaml (`ulib/ml/FStar_List_Tot_Base.ml`), so `isEmpty` is an
external, so rule 4 of §5.0.1 froze every type its signature mentions --
including `Prims.list`.  A monomorphic clone would name a declaration the
hand-written realization does not define.  That is a decision, and it has a
culprit worth printing.

`record_parents` also records, for each type, an external whose signature
mentions it, and the message names it.  `tests/custard/ListC.fst` pins the
result.

What it does *not* do is change the decision.  A module realized in OCaml has
no C counterpart, and honouring `realized_modules` under the C backend is
arguably wrong for that reason -- `isEmpty` could simply be compiled there,
and would then be rejected for the honest reason, that a cons list is a
recursive datatype and a C struct cannot contain itself.  That is a larger
change than a diagnostic, it touches every C and krml test, and it is not
what round 35 asked for; it is written down here as the next thing.

## 32 After the attribute

Rounds 36 and 37, and between them they close the question §12.3 opened.

With `normalize_for_extraction` honoured, all four EverParse CDDL entry
points extract to clean C from a completely unpatched tree, in 11-19 s, with
no `validate_typ`, no `list`, no `char *`, no warning of any kind, and
`gcc -Wall -Wextra` silent.  Round 36 also discharged the caveat that had
been carried since round 11: the generated C was executed, over the same
12,109 CBOR vectors, against an independent pure-Python decoder, with **0
mismatches** for `bool`, `uint` and `bytes`, and then rebuilt under
`-fsanitize=address,undefined -fno-sanitize-recover=all` and re-run over all
10,392 malformed inputs with **0 errors**.

### 32.1 The specializer does no work at all

The number that matters is not the 11 s.  It is this:

| entry point | specializations |
| --- | --- |
| `bool` | 0 |
| `uint` | 0 |
| `bytes` | 0 |
| `signoutputargs` | 7 |

Round 31, same program, was **643**.  `Mono.norm` is 152 ms of the 19 s
`signoutputargs` run; `Monomorphize` itself is 9 ms.

That is §12.3 resolving itself rather than being solved.  Producing
specialization keys was expensive because the keys were normal forms of terms
that are only small when shared — but those terms only ever reached the
specializer because the interpreter had not been reduced away first.  Reduce
it first, as the program asked, and there is no polymorphism left to
specialize.  The time `signoutputargs` does spend is `norm`, which is the
reduction the programmer requested, not overhead.

So the three rounds spent on §30.15's names, §30.17's fallback and §30.14's
dead binders were all fixing the symptoms of one missing pre-pass.  They are
not wasted — every one of them is still load-bearing on some other program,
and §30.17's fallback is what got `signoutputargs` off error 365 in the first
place — but the ordering was wrong, and the right lesson is §31's: read what
the program says before inferring it.

#### The controlled comparison

Round 36 reported that re-applying the reviewer's 34 `[@@@monomorphize]`
annotations produced byte-identical C, and read that as the two routes being
equivalent.  It was a confounded control: with the attribute honoured the
interpreter is reduced away before monomorphization can trigger, so the
result showed only that the annotations had become a no-op.

Round 37 removed the confound by stripping all 76 `normalize_for_extraction`
occurrences and measuring four configurations.  Neither mechanism reproduces
round 35 exactly (45/131/95/167 s, all four on error 368).  Annotations alone
get **2 of 4**, reproducing round 35's byte counts exactly.  The attribute
alone gets **4 of 4**.

And blanket-translating the delta whitelist into annotations makes things
*worse*: `custard_compile_time` at all 98 `sem_attr` sites breaks `bool` and
`uint`, which the annotations alone had fixed, by dragging the CBOR spec AST
into the program — and `signoutputargs` then gives error 372 naming
`validate_map_group`, which carries `sem_attr` and is also a genuine runtime
Pulse function.

That is the sharpest statement of §31's argument, and it came from the person
who had proposed the alternative.  **`sem_attr` and `custard_compile_time`
are not the same predicate.**  `sem_attr` says "unfold this when computing
the semantics"; `custard_compile_time` says "every application of this is
known at extraction time".  A per-use delta instruction does not translate
into a per-definition promise, and 64 annotations across library, spec and
generated code still get 2 of 4 where one attribute the program already
emitted gets 4 of 4.

### 32.2 A chain entry is a term

The chain of §31.2 paid for itself in the round after it landed: the
`Prims.op_Less` that had cost the reviewer a round and been given up on was
located from one error block on the first try, at `CDDL.Spec.AST.Base.fst:799`.

It also had a bug of exactly the shape §30.15 had.  A chain entry is a
specialization **key**, and a key is a term rendered by `string_of_key`, so
it is as big as the term is.  §30.15 bounded the name Custard *emits* —
`hint_of_cty` feeds the C identifier — but not the key it *reports*, and
those are different strings.  With §30.17's fallback keying on the argument
as written, an unreduced `Mkbundle?.b_parser` reached a diagnostic and
printed **6,425,658 characters on one line** of a 6,426,280-byte error block.

`Extract.clip_chain_entry` bounds each entry to 200 characters and says how
much it dropped.  A prefix is the right part to keep: the lid comes first in
a key, so the prefix says which definition, and the instantiation that
follows is what the rest of the chain is already saying.  `PrintC`'s chain is
bounded the same way, on principle rather than on evidence — a chain is not a
place where an unbounded string may appear on the strength of it usually
being short.

`tests/custard/WideChain.fst` is §30.17's doubling record with a `Mono`
binder that keys on it and a body that fails: a 16,372-character key, and a
727-byte diagnostic.  And every reject test now asserts that its whole
diagnostic is under 100 KB, which is the check that would have caught this
without anyone reading the output.

### 32.4 A public surface

Round 38 answered the objection §32.3 raised against `extern "C"` and headers,
by removing it rather than arguing with it.

The objection was that exporting a name means committing to it, and §30.15's
specialization hints are explicitly *hints* — bounded, collision-suffixed, and
free to change when the monomorphizer's input changes. That objection stands
and nothing below relaxes it.

What removes it is the observation that the consumer does not want a
specialization. EverParse's COSE, at `src/cose/c/`, is a production consumer
already in tree: `COSE_Format.c` includes `CBORDetAPI.h` and calls 44 distinct
`cbor_det_*` symbols across a translation-unit boundary. Compile Custard's
whole-program output of `CBOR.Pulse.API.Det.C` and it already exports 43
globally-visible `cbor_det_*` symbols, **none carrying a hint and none
carrying a collision suffix**. That is not luck: `CBOR.Pulse.API.Det.C` is the
API boundary and is monomorphic there, so nothing at that boundary is a
specialization.

So the set the option may touch is not "any definition" but exactly the set
`is_public` already computes — a `Root`, named by `--custard_entry` or
`--custard_entry_module`, emitted with external linkage and declared in the
generated header. Naming a definition that way is already the only route a
caller Custard cannot see has, so the public surface is a decision the user
has made and not one inferred here. `build_renames` additionally checks
`n.spec = None`, on the name rather than on the flag, because the guarantee
wanted is about the name.

`--custard_c_no_prefix M` emits the public definitions of module `M` under
their unqualified identifiers, as krml's `-no-prefix` does. The map is keyed
by `string_of_name` and consulted in `c_name`, so a rename reaches the
definition, its prototype and every call site alike: this is one C name for
one IR name, not a second name for the same thing.

Two definitions wanting one name, or a name already some other declaration's,
is **error 374**. Not a silent suffix — the point of the option is that the
caller writes the name, so producing a name the caller did not ask for is
worse than refusing. A module named but contributing nothing is **warning
375**, because that is a typo or a forgotten `--custard_entry_module` and
silence there costs a round.

The `extern "C"` guard is unconditional, and goes *after* the includes. Never
around them: a system or an external header brings its own linkage decisions,
and wrapping one is how a C++ consumer acquires an unresolvable `std::`
symbol.

`tests/custard/Export.fst` is the COSE shape in miniature. Three roots
exported unqualified, one unnamed `helper` that stays `static` and is absent
from the symbol table, and one polymorphic `countdown` that reaches the unit
only as a specialization and keeps its hint. It is extracted twice — once with
a `main` and run standalone, once without, as a library — and
`ExportUser.cpp`, a hand-written consumer, is compiled **as C++** and linked
against it. The C++ half is the assertion: strip the guard and the three calls
fail to link as `widget_add(unsigned int, unsigned int)`, which is the check
being made. `nm` confirms the exported and the hidden halves.

`tests/custard/ColB.fst` is the collision.

What this does **not** do, and should not: make a specialization exportable.

### 32.3 What is not done

- **`realized_modules` under the C backend** (§31.3).  Still the next thing,
  still deliberately separate.
- ~~**`extern "C"` and headers**~~ — done in §32.4.
- **Stacked attribute sets.**  `[@@a] [@@b]` is Error 131 in F\* itself, not
  in Custard; anyone inserting an attribute mechanically has to merge into
  the existing set.  Noted because it will bite the next person who scripts
  such an edit.

## 32.5 An external has no body

A second reviewer ported [Kuiper](https://github.com/fstarlang/kuiper) — a
Pulse DSL for verified CUDA kernels, currently extracted through
`--codegen krml` plus a ~1200-line, ~250-rule Krml plugin — onto Custard and
reported three bugs. This one is the serious one.

`[@@@monomorphize]` on a binder of an *external*:

```fstar
[@@custard_extern "kpr_launch"]
assume val launch ([@@@monomorphize] d : desc) : UInt32.t
let go (k : UInt32.t) : UInt32.t =
  launch ({ nblk = 1ul; f = (fun tid -> UInt32.add_mod tid k) })
```

produced

```c
extern uint32_t kpr_launch;      /* an object */
uint32_t CMwe3_go(uint32_t k) { return kpr_launch(k); }
```

Specialization works by substituting the argument into a **body**. An external
has none, so the argument is substituted into nothing: the signature loses the
binder, the descriptor is discarded, and `kpr_launch` — one fixed C symbol —
never learns what it was. `external_ty` did the substitution faithfully and
there was nothing left to do it to.

The reported form does not compile, which is how it was found. The form that
matters is the one nobody reported. With a *closed* argument there is no
capture, so there is no arity mismatch either:

```c
uint32_t CMwe3b_go(uint32_t k) { (void)k; return kpr_launch; }
```

That compiles, and the launch never happens. A silent miscompilation, which is
the class §6 refuses everywhere else, and it had no test.

**Error 376.** A `Mono` value binder on an external is rejected. A `Mono`
*type* binder stays allowed and is unaffected: a type argument is substituted
into the signature, and the signature is the whole content of a type argument,
so nothing is lost. That distinction is the fix — the check is `Mono`, an
argument supplied, and `not (is_type_binder ...)`.

`tests/custard/MonoExtern.fst`.

## 32.6 Storing a type is not an existential

The second bug, reduced by the reporter to:

```fstar
class sized (t:Type0) = { sz : SZ.t; dflt : t }
noeq type desc = | D : (ty:Type0) -> {| sized ty |} -> len:UInt32.t -> desc
let dlen (d:desc) : UInt32.t = match d with | D _ len -> len
let go (d:desc) : UInt32.t = dlen d
```

Error 364, advising an annotation. Their diagnosis was that §30.14 was not
firing through a constructor field, and that "nothing observable depends on the
existential" since `dlen` reads only `len`.

That diagnosis is wrong, and the report is right anyway. `desc` genuinely has
no C representation: the `sized ty` field's layout depends on `ty`, so no
single `struct desc` exists, whatever `dlen` happens to read. Rule 4b is
correct here and there is nothing to fix in the classification.

What is wrong is that **the error says none of that.** It reports rule 4b's
consequence — "there is nothing to specialize on" — and then gives two pieces
of advice, both unavailable: annotate the enclosing binder, which only moves
the problem to that function's caller and does so forever; or drop the
annotation on binder 0, which nobody wrote. §30.4 already has the right words
("a field of kind `Type0` whose siblings' types mention it makes the type an
existential package") but they appear only in a warning that fires when you
write the attribute on a *field* — that is, only after you have followed the
bad advice.

`Mono.existential_field` now finds the constructor and the field responsible,
and error 364 says so, states that no annotation changes it, and gives the
remedy that does exist: make the type a parameter of the inductive rather than
a field of the constructor.

### Rule 4b was too wide

Writing that down exposed the real defect. `ctor_stores_type` asked only
whether a constructor stores a `Type0`. But

```fstar
noeq type desc = | D : (ty:Type0) -> len:UInt32.t -> desc
```

is not an existential. Nothing mentions `ty`, so the field is erased like any
other type (§5.1), and what remains is one `UInt32.t` with a perfectly uniform
representation. Rule 4b made every binder of this type `Mono` for no reason —
error 364 on a program that compiles fine.

The condition is dependence, not storage, and it is the condition §30.4's
prose already stated. `ctor_stores_type` now requires that a *later* field's
type mention the stored one. `StoredType.fst` is the case this admits: `desc`
newtype-collapses to `uint32_t` and `dlen` is the identity.

## 32.7 A misattributed realization

The third: error 368's advice for a type frozen by §5.0.1 rule 4 asserted that
the external freezing it "is a hand-written realization for the OCaml backend,
and there is no C counterpart". For a `custard_extern` that is false — it is a
C symbol the program named, and the reader is sent looking for an `.ml` file
that does not exist. `frozen_by_target` records the target symbol when there is
one, and the sentence now names it.

## 32.8 What Kuiper asked for and has not got

Recorded because the answers are design decisions, not omissions.

- **Float widths.** `TInt of signedness & width` has no float; `Kuiper` needs
  `Float32`/`Float64` and also `Float16`/`BFloat16`. This is the largest of the
  asks and the most clearly right: a float add currently has to go through a
  `custard_extern` and stays an opaque call where `u32` gets `+`.
- **A rule that can emit a declaration.** The reporter withdrew half of this
  themselves on finding that `[@@@monomorphize]` already performs
  capture-to-parameter lifting — which it does, and that *is* the kernel-lifting
  transformation. What is left is naming the specialization and attaching flags
  to it, which is a smaller thing than closure conversion.
- **Karamel declaration flags.** `CPrologue`/`CEpilogue`/`Comment`/`CInline`
  through to `K.Prologue` etc. Small, and blocking: without `__device__` the
  generated `.cu` does not compile.
- **`ESizeof`.** Small.
- **Indexed external types** — `wmma::fragment<half,16,16,16,...>`, whose C
  spelling is a function of the type's indices. `custard_extern` takes a fixed
  string.
- **Observing type declarations**, for a rule that projects fields out of a
  record argument. May be recoverable from `ERecord`/`EProj`, which do survive.

## 32.9 The header is the API

Round 39 linked §32.4's output against the real COSE consumer. Not a
reproduction — `src/cose/interop` builds `signtest`/`verifytest` from the
checked-in, EverParse-generated `COSE_Format.c` plus OpenSSL, and cross-checks
against the independent `pycose`; Custard's `CBORDet.o` was substituted for
karamel's and nothing else changed. It signs, `pycose` verifies it, it verifies
`pycose`'s signature, and rebuilt under ASan/UBSan the three results are the
same with no findings.

Three things worth recording from that.

**A strip is sufficient; no rename map is needed.** All 35 `cbor_det_*` symbols
COSE leaves undefined resolve against the 44 the unqualified output exports.
The question §32.4 left open is closed.

**The generated types are ABI-identical to the hand-written header.** COSE
never includes Custard's header — it includes `CBORDetType.h` and links across
the boundary — so the link is only meaningful if the layouts agree.
`cbor_det_t` is 40/8 both ways, map entry 80, both iterators 32.

**The renaming is purely nominal.** Re-applying the module prefixes
mechanically to the renamed output and diffing against the ordinary output
leaves one difference: a definition that became a root moved to the top of the
file, because it is no longer `static`. No other line differs.

### What the flag did not rename

Types. The header declared

```c
CBOR_Pulse_Raw_Type_cbor_raw cbor_det_parse(uint8_t *input, size_t len);
```

so a consumer could call the function but could not spell what it returned.
For COSE that costs nothing, since COSE brings its own header and needs only
link-level compatibility — but it means the generated header could not be used
*by itself* as the public API, which is what §32.4 claims it is. The function
names were the API's and the type names were still internal spellings.

A type has no linkage, so `is_public` has nothing to say about one; that is why
the first cut skipped them. But the header already carries the unit's whole
type language on purpose, and a consumer that cannot name the type of what it
just called does not have an API. So a named module's types are renamed too,
and so are its constructors — a variant's enum tags are equally part of what
the header exports, and `c_tag` now goes through the same map. `struct_tag`
derives from `c_name`, so struct tags follow for free.

`tests/custard/ExportUser.cpp` now writes `widget w = widget_make(4, 9);` and
compares against `WLARGE`, in C++, across the boundary.

### `--custard_c_no_prefix` needs `--custard_entry_module`

Worth stating plainly, because the reporter hit it: the flag only bites on
declarations that are *already* part of the interface. Naming a module without
also making its definitions roots leaves them `static` under their qualified
names. That is warning 375. The COSE invocation needs both flags for two
modules — `CBOR.Pulse.API.Det.C` and `CBOR.Pulse.API.Det.Dummy`, which is what
the karamel baseline passes `-no-prefix` for — and repeating the flag composes.

## 32.10 One pair of parentheses

`c_expr` parenthesizes every operator application, so a condition arrives
already wrapped and `if (...)` added a second pair. clang calls that
`-Wparentheses-equality` and emitted it 78 times on one generated file; gcc
`-Wall -Wextra` never mentioned it, which is why it survived this long. A
consumer building with `-Werror` under clang could not use the output, so it is
not cosmetic.

`is_group` decides whether a string is one parenthesized group — the leading
paren must be the one the trailing paren closes, or `(a) && (b)` would lose its
meaning when stripped. `unparen` drops that pair for a condition; `negate`
uses it in the other direction, adding parens for `!` only when the operand is
not already a group.

## 32.11 Not ours

Two items from round 39 recorded because they will be met again.

An EverParse proof — `...ZeroOrMore.Aux2.Lemma13` — broke on the `master`
merge, deterministically, at the trailing `()`, and passes at
`--z3rlimit_factor 4`. The goal shape matches `e4e983c9fa` "Push the expected
postcondition into the body's expected type by default", whose own series
carried `de044176e8` "Drop four of the rlimit increases the postcondition push
needed". Proof fragility from an upstream change, not from Custard, and it
belongs to EverParse.

The COSE baseline fails with `TypeError: Bytes cannot be decoded as COSE
message` under `cbor2` 6.x. The repo's Makefile pins `'cbor2<6'`.

# 33. Pulse reaches C

Round 40 is the second reviewer's, and it is the first report from a program
that is Pulse the whole way down. Kuiper is a Pulse DSL for verified CUDA
kernels, extracted today through `--codegen krml` and a ~1200-line karamel
plugin, and its 396 modules verify against this branch unchanged.

Three of the four things it found are the same thing seen three times: the
attribute that selects a specialization, the definition it is written on, and
the diagnostic that fires when neither worked, each of which handles a Pulse
`fn` worse than it handles the F\* function it desugars to. What follows is
in the order they have to be fixed, which is the reverse of the order they
are met.

## 33.1 A body that is a lambda is not a closure

```fstar
let ap (f : U32.t -> U32.t) (r : U32.t) : U32.t = f r
let go (k : U32.t) : U32.t -> U32.t = ap (fun x -> U32.add_mod x k)
```

```
let CMwe9.go (k: u32) : u32 -> u32 [Pure] = fun (x: u32) -> `+.u32`(x, k)
```
```
* Error 368: a lambda that captures a local variable has no C
  representation, in CMwe9.go.
```

The lambda captures `k`, and `k` is `go`'s own parameter — so the thing it
captures is a thing `go` already has, and the "capture" is an artifact of
where the binder was written. `let f x = fun y -> e` and `let f x y = e`
denote the same function and compile to the same code in every target
language Custard emits.

§25's expansion did not do it, and could not have. It works by *applying* the
body to a fresh variable, and a lambda applied to a fresh variable is a
redex, not a parameter. It also refused to consider the case at all, because
§25.3 admits only a *cheap* body and a lambda is not on the list — which is
the right list read the wrong way round: the list exists to bound how much
work is repeated per call, and evaluating a lambda performs none. The body is
not run. That is what a lambda is.

So the absorption is separate from the expansion and unconditional, and takes
the *declared* codomain rather than the body's own type. Those can disagree —
a reified `Tac` body is a match whose arms have the concrete type and whose
declaration has `TAny` — and that disagreement is what the coercion pass is
for. Taking the body's type would silently agree with it instead, and the
`Obj.magic` that made the arms typecheck would never be inserted. `make
custard` is what says so: with the body's type the extracted compiler does
not build, in `FStar.Tactics.V2.Logic.cur_goal` and
`FStar.Tactics.Typeclasses`.

## 33.2 A lambda argument is cheap too

That is one of the two shapes Pulse produces. The other is what `eta_reduce`
leaves of an `fn` with more than one binder:

```
let PMwe.use (k: u32) : ref u32 -[I]-> unit [Pure] =
  PMwe.apply_twice (fun (x: u32) -> `+.u32`(x, k))
```
```
* Error 368: the partial application of PMwe.apply_twice has no C
  representation, in PMwe.use.  It is applied to 1 of its 2 arguments.
```

`r` moved from the binder list into the result arrow, and the call became
partial. This *is* §25's case, and every guard on it passes — the callee's
arity is known, the demand is one argument, the callers supply it — except
that `cheap_expr` rejects the lambda in argument position, for the reason
above and just as wrongly.

`EOp` joins it, for the same reason `ECast` was already there: an operator
application is bounded work that allocates nothing. A memory operation is an
`EOp` too, since Pulse writes `BufRead` and `BufWrite` as one, and it is
excluded by the effect test rather than by the shape — which is where that
distinction belongs, and it is worth checking that it really is excluded
there, because nothing else would catch it.

## 33.3 An attribute is written on the lambda

With both of those fixed the specialization still did not happen, and
deleting the attribute produced a byte-identical dump — the failure mode with
no evidence at all.

`[@@@monomorphize]` is written on a binder, and a classification reads
binders off the definition's *type*. Those are two different lists that
usually agree. Pulse's `tm_arrow` builds the elaborated arrow through
`mk_arrow_with_name`, which builds its binder with `attrs = []`, so for a
Pulse `fn` they do not: the attribute is on the definition and absent from
its type, and rule 3 never fires.

That could be fixed in Pulse, and arguably should be. It is fixed here
anyway, because the narrower fix is also the more correct one. §19.4 already
argues that the lambda is the more faithful of the two lists — it is what
makes the classification as long as the definition really is — and this is
the same argument about a binder's attributes rather than about how many
binders there are. So the two are unioned, positionally, rather than one
preferred: a type can have binders the lambda does not, a projector being
written with fewer abstractions than its arrow has, and each list is
authoritative exactly where the other says nothing.

`tests/custard/pulse/PulseMono.fst` needs all three of these to compile, and
checks its own answer when it runs, so a specialization that closed over the
wrong value is a nonzero exit rather than something to be read out of the C.

## 33.4 A correct rejection is not a bug report

§32.6 gave error 364 an explanation for an existential type: which
constructor stores the `Type0`, and which later field's type mentions it.
Kuiper takes neither path 364 is on. It meets the same type as a field of
runtime data, and gets 368:

```
* Error 368: the type variable 't has no C representation, in
  Kuiper.Sized.sized.
  --custard_monomorphize_types is already set, so this type is one the
  monomorphization pass did not reach (section 5.0.1).
  That is a Custard bug, not a configuration problem: please report it.
```

It is not a Custard bug. It is the existential of §30.3, correctly rejected —
and the message asks the reader to file an issue about it. That is worse than
saying nothing: a wrong explanation is acted on.

The reason 368 could not say what 364 says is that by the time the backend
sees the type, the `Type0` field is erased and what is left is a `TAny` or a
type variable with no visible cause. So the cause is carried rather than
inferred: `Existential` is a type flag the extractor sets from
`Mono.existential_of_lid`, and nothing reads it to make a decision — the type
is rejected either way, by whichever of its fields lost its representation
first. It exists so that the rejection can say why.

It is looked up along the whole `Reached through` chain and not only at the
head, because the type that lost its representation is usually a *field's*
type and the existential is the record above it — which the chain already
names. And the branch it replaces stands down rather than print both: "please
report a bug" and "this is not a bug" in one message is worse than either.

`ExistChain.fst` pins the new sentences and, through a new `NOEGREP_` hook on
the reject rule, the absence of the old one. A replaced sentence has to be
pinned as absent or nothing notices it coming back.

## 33.5 Not fixed

`--custard_unit` and `--custard_link` are implemented for the OCaml backend
only (error 155), so the separate compilation §12 describes is not available
to a C consumer yet. Kuiper ships 62 generated `.cu` files and cannot treat
whole-program-per-kernel as a workaround. Recorded here because the build
model was agreed and the implementation was not; it is the largest thing this
report leaves open.

# 34 Rules, attributes and captures

Round 41, from the Kuiper reviewer. `Kuiper.For.for_loop` works with
`[@@@monomorphize]` now, and the loop bodies compile with their captures
lifted to parameters; §33's three fixes were what it needed. What that left
was one question about the *ordering* of the extraction, and it is the
question this section answers.

## 34.1 A rule sees its arguments reduced

Kuiper's host side hands `launch_kernel_full` a `kernel_desc` whose
`shmems_desc` field is a `list shmem_desc`, and `shmem_desc`'s constructor
stores a `Type0` that a later field's type mentions. That is §30.3's
existential package, and §33.4 now correctly says so: error 368, no C layout,
no annotation that changes it.

The remedies §33.4 offers do not apply, and the reason is worth recording.
The stored type is not used to hold a value; it is used to *build* a type.
`c_shmem (SHArray ty len) = larray ty len`, and `c_shmems` folds a list of
descriptors into the tuple type of the arrays a kernel receives. An index
cannot replace the type because the program does not case on it, it computes
with it, and the type cannot move onto the inductive because the list is
heterogeneous, which is the point of it.

But the descriptor is never runtime data either. It is compile-time input to
code generation: `inline_for_extraction noextract`, a literal at every call
site, and today's krml plugin destructures the whole thing during extraction
and emits a launch macro. The reason it reaches the backend at all is that
Custard had nowhere else to put it.

The place to put it is a rule (§8). §8.2's table is consulted in step 1 of
the extraction loop, before the definition is looked up, so a name with a
rule is never requested and never emitted; the rule builds an IR term from
the call's arguments instead. The reviewer's question was whether that is
usable here -- whether a `Rule_prim` sees the descriptor as a structure it
can walk, or as an opaque reference to the `let` that bound it, and whether
the descriptor's type has to have a C representation before a rule is
consulted at all.

It sees a structure, and it does not. `tests/custard/plugin/CustardRulePlugin.fst`
is the worked example, which is the other half of the answer: `register_rule`
was exported, documented and never demonstrated, and the reviewer could not
find out from the tree what a rule receives.

Two properties, both now pinned by that test.

*Reduced.* A `let`-bound descriptor is unfolded before the rule sees it,
provided the definition is one the extractor may unfold. The test's

```fstar
inline_for_extraction noextract
let kd : kdesc = { kname = "kernel";
                   shmems = [ DArr U32.t ({ sz = 40ul; dflt = 0ul }) 10;
                              DArr bool  ({ sz = 2ul;  dflt = false }) 2 ] }
```

arrives at the rule as

```
CustardRuleTest.Mkkdesc("kernel",
  Prims.Cons(CustardRuleTest.DArr(CustardRuleTest.Mksized(40<u32>, 0<u32>), 10),
  Prims.Cons(CustardRuleTest.DArr(CustardRuleTest.Mksized(2<u32>, false), 2),
  Prims.Nil)))
```

-- a record literal and a chain of `Prims.Cons`, with the heterogeneity
intact: `0<u32>` and `false` sit in the same list, at the same field of the
same constructor, and nothing has had to give them a common representation.

*Pre-layout.* Rules run during extraction, before §6's passes, so a
single-constructor type is still an `ECtor` and not yet the `ERecord` the
final dump shows. A rule matches on the constructor, not on the
representation. Type arguments are already gone, though -- `DArr` is
declared with three parameters and arrives with two -- so a field is at its
position among the *retained* arguments.

The 368 does not fire because it cannot: it is raised by the backend, and by
the time the backend runs, `Simplify.dce` has removed the descriptor's types
as unreachable. Nothing in the program mentions them any more, because the
rule consumed the only mention. The test asserts exactly that -- neither
`CustardRuleTest_desc` nor `_sized` nor `_kdesc` appears in the generated C
or its header -- and then compiles and runs the result, which returns 0
because the plugin added 40 and 2 together while the extraction was running:

```c
static uint32_t CustardRuleTest_main(void) {
  uint32_t r = (((uint32_t)3U) + ((uint32_t)42U));
  if (r == ((uint32_t)45U)) return ((uint32_t)0U);
  else return ((uint32_t)1U);
}
```

So the answer to the ordering question is that there is no ordering problem:
a rule is consulted before the definition, its arguments are reduced, and
what it does not use does not survive. Kuiper's host side is a plugin rule
and needs nothing further from Custard.

The example is wired into `make custard`'s `plugin` target, which already
compiles a plugin *with* Custard and loads it into a Custard-built compiler.
`CustardRulePlugin` is a third root there, and a root for the same reason the
other two are: a module that exists for its initializer has to be named or
nothing reaches it (§4.4). `FStarC.Custard.Builtins.register_rule` and its
two chaining forms are now in `src/custard/entrypoints.txt`, since a plugin
calls them through no request the extraction can see.

`mk/custard-rule.mk` is a separate makefile only because the dependency graph
of the test program has to be generated by the Custard-built compiler and
then included, and a recipe cannot include a file it has just written. The
closure is rechecked rather than reused: §12.10's limitation is that a
Custard-built compiler cannot read a dune-built one's `.checked` files.
`--lax` is enough, and makes the 37 modules take about fifteen seconds.

The rule itself fails loudly on a shape it does not expect, and says which
shape it got. A rule that silently accepts the wrong one is worse than one
that stops: the wrong shape means the descriptor did not reduce, and the
program that comes out is then wrong rather than absent.

## 34.2 A recognized attribute in an unrecognized position

§33.3's bug had no evidence: two binder lists existed, one carried the
attribute, the other was consulted, and nothing compared them, so deleting
the attribute produced a byte-identical dump. Asked what would have caught
it, the reviewer's answer is that the general question -- "did this attribute
have an effect?" -- is not the one to ask, and "was it read?" is, being a bit
that can be set at the point of reading.

That is still invasive. The cheaper half is not: the set of attributes
Custard reads is closed and small, and each is read in exactly one kind of
position. Written anywhere else it can never do anything, and *that* is
decidable here and now. `[@@custard_extern]` on a binder, `[@@custard_opaque]`
on a field, `[@@custard_inline_field]` on a declaration: none of them can ever
have an effect, and each one is a reader who thinks they have configured
something.

`Extract.check_decl_attrs` runs once per definition, from `binder_classes` --
which is cached per lid, so the report is not repeated once per call site --
and `check_binder_attrs` additionally runs over constructor fields from
`extract_inductive`, where §30.4's `[@@monomorphize]`-on-a-field warning
already lived. Warning 371 gains four more shapes:

- a declaration-only attribute on a binder (`custard_extern`,
  `custard_c_header`, `custard_opaque`, `custard_no_monomorphize`,
  `custard_compile_time`);
- a field-only attribute on a declaration (`custard_inline_field`);
- `[@@custard_c_header]` with no `[@@custard_extern]` beside it, which is a
  position error of a third kind: the header is read only while building the
  rule the extern attribute asks for.

Each report says where the attribute does belong, since a reader who wrote it
in the wrong place knows what they wanted and not where to write it.

The binders it checks come from both the arrow and the lambda, for §19.4's
reason and §33.3's -- an attribute written on either should be seen -- and
are merged *positionally* rather than concatenated. Concatenating reports the
ordinary case twice, since the two lists usually describe the same parameters
and carry the same attributes.

`tests/custard/AttrPos.fst` has one of each of the four.

## 34.3 A block argument's captures

Round 40's reporter checked `[@@@monomorphize]` on a `fn` binder against a
real separation-logic loop combinator and a `fn` block that captures a `ref`
and a value from the caller's frame, neither of them a loop parameter, and
got a C `while` loop with both captures lifted to parameters and the ghost
apparatus gone. That was measured downstream, in a tree Custard's own suite
does not build. `tests/custard/pulse/PulseForCapture.fst` reduces it to
Pulse's own library so that it is tested here:

```c
static void PulseForCapture_for_upto__0(uint32_t *tmp, uint32_t tmp1, uint32_t n) {
  uint32_t i = ((uint32_t)0U);
  while (true) {
    if (!((i < n))) { break; }
    uint32_t vi = i;
    uint32_t v = tmp[((size_t)0ULL)];
    tmp[((size_t)0ULL)] = (v + tmp1);
    i = (vi + ((uint32_t)1U));
  }
}

static void PulseForCapture_accum(uint32_t *r, uint32_t k) {
  PulseForCapture_for_upto__0(r, k, ((uint32_t)10U));
}
```

The loop is compiled once per *body* rather than once per call, and the
body's free variables can only reach it as arguments. `main` checks its own
answer, so a capture taken from the wrong frame is a nonzero exit rather than
something to read out of the generated C.

Writing it turned up one thing that is not obvious and that Kuiper's
`for_loop'` already gets right. The invariant has to be an explicit `slprop`
parameter. Written the other way --

```fstar
fn for_upto (r : ref U32.t) (n : U32.t)
            ([@@@monomorphize] body : x:U32.t -> stt unit (exists* v. r |-> v) ...)
```

-- the body's type mentions `r`, so §3.1 rule 5 carries the demand from
`body` to `r`; `r` is a runtime parameter of the caller, and the result is
error 364, "there is nothing to specialize on". Naming the invariant instead
puts a ghost binder in the demand's way, which rule 1 drops before rule 5 can
reach through it.

## 34.4 Not fixed

§33.5 stands: `--custard_unit` and `--custard_link` are OCaml-only (error
155), and separate compilation for a C consumer is the largest thing these
reports leave open.

The general form of §34.2 -- a bit per recognized attribute, set where the
attribute is read, and a report where no pass set it -- is not implemented.
It is the right answer to the failure mode §33.3 had, and it is a change to
every reading site rather than a check that can be added in one place.

# 35 The public surface, and checks that do not need a compiler

Round 40's verification, from the EverParse reporter. Everything §32.9 and
§32.10 claimed holds at scale: the COSE interop signs, verifies and verifies
`pycose`'s signature with the type and constructor renames active, all 35
undefined `cbor_det_*` still resolve against the 44 exported, CBOR direct-to-C
is behaviourally identical to golden on 1,717 valid and 10,392 malformed
inputs, the krml-to-Rust path is byte-identical, and the four CDDL entry
points differ from their round-38 goldens in parentheses and nothing else --
0 non-parenthesis differences over 201 changed lines, 70,002 to 69,840 bytes
and 125,467 to 125,251, entirely in removed characters.

Two things came out of it, and neither is a bug in what was measured.

## 35.1 A public API whose types are generic

The report drove the real CBOR API from C++ off nothing but the generated
header and three typedefs, and made the case that the type rename map §32.9
left open should not be built: two of the three typedefs name types
`--custard_c_no_prefix` already renames, and the fourth group of names --
the `cbor_det_*` abbreviations -- are *the consumer's* names, which is why
the source writes them as abbreviations in the first place. Custard cannot
know an abbreviation the consumer chose. That question is closed: not built,
on the report's advice, and §32.9's open item is withdrawn rather than
deferred.

The third typedef is the finding:

```c
typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__cbor_raw
        cbor_det_array_iterator_t;
```

It cannot be written with a source-level name at all, because the type on
the interface is not a module's declaration but a *monomorphized instance*
of one. `--custard_c_no_prefix CBOR.Pulse.Raw.Iterator` does not help and
correctly says so with warning 375. The exclusion is deliberate and stays:
§30.15's hints are depth-bounded, clipped to 48 characters and
collision-suffixed, so they are precisely the names that may change when the
monomorphizer's input does, and nothing outside the translation unit may
depend on one.

What was wrong is that nothing said so. A consumer reads the header, sees a
name, writes it down, and finds out later. The condition is decidable at the
point of printing -- a public prototype goes in the header, and a `TApp` in
it whose name has a `spec` is a generated name the consumer has to spell --
so `PrintC.check_interface_names` reports it. Warning 377, once per type
rather than once per definition that exposes it, naming one definition that
does:

```
* Warning 377:
  - Custard: the type `ExportGen_cell__uint32' is part of this unit's
    interface -- ExportGen.get has it in its signature -- but its name is
    generated.
  - It is a specialization, so the name carries a hint built from the
    monomorphizer's input and may change when that input does.
    --custard_c_no_prefix does not rename specializations.
  - A consumer that must spell it should typedef it once, in its own header,
    rather than depend on this name throughout.
```

Only types the unit actually declares are reported: an abbreviation that was
unfolded leaves no name in the header for anyone to depend on.
`tests/custard/ExportGen.fst`.

## 35.2 A property, not a warning

§32.10's fix was checked by the disappearance of clang's
`-Wparentheses-equality`, 78 to 0. The report shows that check is weaker
than it looks, because clang's warning is *shape* sensitive:

```c
int t1(int a,int b){ if ((a==b)) return 1; return 0; }    /* warns  */
int t2(void)       { if ((g()==1)) return 1; return 0; }  /* silent */
```

With a call on the left, clang says nothing. So a surviving redundant pair
around a call-comparison would have passed a `-Werror` build, and `-Werror`
was the whole check. The report then checked the property directly instead,
with a paren matcher over the real 198 KB `CBORDet.c`: of 36 conditions
beginning with `(`, zero were a single redundant group. That is the right
check and it does not need a compiler.

`tests/custard/checkgroup.py` is that matcher, generalized from `if` to every
position and run on every C file all three suites generate. It reports any
group whose entire content is another group, skipping comments and string and
character literals, and skipping a parenthesis that is part of C's syntax
rather than a grouping -- `f((x))` is one argument that happens to be a
group, not two pairs, so the parentheses of a call, a parameter list or a
cast are not candidates. The keywords whose own parentheses do enclose an
expression are.

Run over output that `-Wall -Wextra -Werror` had accepted, it found three
sites, all of the class the report predicted would hide:

- the exit test of a Pulse `while`, `if (!((i < n)))`, which built its
  negation by hand instead of going through `negate`;
- `malloc((((size_t)1ULL)) * sizeof(T))`, where the allocation wrapped a
  length that `c_expr` had already parenthesized;
- `(size_t)(((size_t)1ULL))` in the loop that fills a fresh run, the same
  length in the same statement.

Every position that needs a parenthesized operand now goes through one
`group` helper, so no site can be the one that adds the second pair, and
`negate` is defined in terms of it. Neither gcc nor clang would have
complained about any of the three: `<` is not a comparison
`-Wparentheses-equality` looks at, and a cast is not one either.

## 35.3 A setting for no test

Wiring `checkgroup.py` into `tests/custard/pulse/Makefile` turned up that the
`CGREP_` and `CNOGREP_` variables that directory had been accumulating were
read by no recipe at all. §34.3's assertions about the specialized loop's
parameters, and round 40's about `PulseMono`, were set and never run.

That is M10φφ from the other side. There, a test had settings and no
registration; here, settings had a registration and no consumer. Both are
silent, and both read like coverage that does not exist. The recipe now
applies them, over the header as well as the source as `tests/custard` does.

`check-settings` is the general form, in both directories and part of `all`:
every variable whose name is a known setting prefix must name a registered
test. It is four lines of `make` over `.VARIABLES`, and it reported four
names on the first run -- all of them hand-written targets with their own
`all:` line, which are listed explicitly rather than made to look like list
entries they are not.

# 36 What a rule may add to the program

Round 42 is the reporter reading section 34 back and reporting what they
found when they used it. Two of the three findings are about the same thing
from opposite sides: a rule can now *add* a call and a function to the
program, and neither the program's bookkeeping nor its output was ready for
declarations that no F* source mentions.

The round also closed the question section 34 opened. `Rule_prim` can
reproduce `hoist`. The reporter extended the rule test's descriptor with a
`kbody : U32.t -> U32.t` written at the launch site over a local, saw it
arrive at the rule as `fun (tid: u32) -> +.u32(tid, c)` -- an `EFun` open in
that local, exactly `hoist`'s input -- computed its free variables, closed
the lambda over them and let section 19.12's `lift_lambdas` push it out. So
`Rule_prim_st` is not needed, and is not being added.

## 36.1 A reference to a declaration that is not there

A launcher rule's whole job is to emit a call to a runtime entry point.
Nothing in the *source* calls that entry point -- that is what makes it a
launcher -- so nothing makes its declaration reachable, so `dce` deleted it.
The output was written with no error and no warning.

It did not compile, which is the good case. The bad case is what the name in
it was: `CustardRuleTest_kcall`, the *mangled* one, and not the `kpr_kcall`
that `[@@custard_extern]` gave it. The declaration was never processed, so
its attributes were never read, so neither its target name nor its header
reached the output. A plugin author's reward for a typo in a name was
invalid C with no diagnostic at all, and a symbol that looks like Custard
ignored an attribute it in fact never saw.

`check_resolved` is error 379. It runs immediately after `dce` -- which is
the pass that can remove the declaration a reference needs -- and before the
passes that rewrite bodies, so the name it reports is the one the rule wrote
rather than a coerced, record-collapsed descendant of it. Every `DLet`'s
body is walked for `EQual` names and each is looked up in the program.

Values only, and value references only. A missing *type* is already rejected
by the backends with a message about the type, and a constructor or a field
resolves to the type that owns it, which is a different question from
whether there is a symbol to link against.

Whole programs only. Under `--custard_unit` and `--custard_link` a unit is
compiled against the units below it and a reference that leaves the unit is
not in this program by design; the C compiler and the linker resolve those.
The check is the whole-program assumption written down, so it holds exactly
where that assumption does.

This is the more valuable of the round's two fixes, and the reporter said so
before it was written: `register_root` stops one cause, and the check stops
every reference to a name that is not there, whatever put it there.

## 36.2 A rule's roots

`FStarC.Custard.Builtins.register_root` takes a `lident` and adds it to the
roots of the extraction, next to the ones `--custard_entry` names. A rule
registers it once, beside `register_rule`:

```
let _ =
  B.register_rule (Ident.lid_of_str "CustardRuleTest.launch")
                  (B.Rule_prim (2, launch));
  B.register_root (Ident.lid_of_str "CustardRuleTest.kcall")
```

Roots are collected before the extraction loop runs, and a plugin is loaded
before that, so the ordering works out with nothing to arrange. A registered
root that is erased is dropped, exactly as `--custard_entry`'s are.

Until this existed the rule test kept `kcall` alive with a dead branch that
existed only to mention it. That is gone.

## 36.3 Lifting a named, decorated function

`lift_lambdas` names what it lifts after the definition it came out of:
`CustardRuleTest_main__lam`. For a device backend that name is not cosmetic.
It is the kernel's symbol, and it appears in profiler timelines, in
disassembly and in the messages a user of the generated code reads. The
descriptor already carries the name the author chose.

```
val lift_named : string -> list flag -> expr -> ML expr
```

The expression must be a lambda. `lift_named` makes it a top-level
declaration under that name, used verbatim -- no namespace, no mangling,
because a kernel symbol read in a profiler is the one thing that must be
predictable -- and returns the `EQual` that names it, which the rule puts
wherever it was going to put the lambda. A second use of the same name is
error 378 rather than a silent overwrite.

The lambda must be closed. Custard cannot close it: only the rule knows what
call it is building, so only the rule can add the captures as parameters and
pass them at the call site. That is what the reporter's own code already
does, and section 36.5 is why it stays that way.

The flags are the second half of the finding, and close a gap open since
round 34. Custard's `flag` type gains `Prologue of string`, `Epilogue of
string` and `CInline`; `Comment of string` was already there and reached
neither backend. All four now reach karamel, and `Prologue`, `Epilogue`,
`CInline` and `Comment` are emitted by the C backend directly:

- `Comment c` is `/* c */` on its own line before the definition.
- `Prologue s` is `s` on its own line before the definition *and* before the
  prototype. CUDA wants `__global__` on both, and a qualifier on one and not
  the other is a redeclaration error, which is a better failure than a
  silently host-side kernel.
- `Epilogue s` follows the definition.
- `CInline` is `inline`. Custard's own `Inline` is a different thing: that
  one substitutes the body and emits nothing.

Custard reads none of the strings.

`lift_named` sets `Root` on what it lifts, because the declaration exists
only because a rule made it and nothing else can keep it alive. `Root` also
meant "public" in the C backend, which is wrong for a lifted function --
usually it is an implementation detail of the call the rule emitted -- so
`Private` now overrides that, and a rule that wants `static` asks for it.

The rule test is the whole mechanism end to end. The descriptor names the
kernel; the rule closes the body over its capture, lifts it under that name
with a `Prologue` and a `Comment`, and calls `kcall` with the kernel, the
block count and the capture. What comes out is:

```
extern uint32_t kpr_kcall(uint32_t (*)(uint32_t, uint32_t), uint32_t,
                          uint32_t);

/* kernel kernel, 42 bytes shared */
__attribute__((noinline))
static uint32_t kernel(uint32_t c, uint32_t tid) {
  return (tid + c);
}
```

`__attribute__((noinline))` rather than `__global__` because the suite's C
compiler has to accept the file; it occupies the same position and is
checked in the same way. The generated program links against a
hand-written `kpr_kcall` and checks its own answer, so the capture reaching
the kernel from the right frame is an exit status rather than something to
read out of the C.

## 36.4 A name is not a computation

A rule that built its call as `EApp (EQual kcall, args)` got a call through a
function pointer:

```
uint32_t (*tmp1)(...) = kpr_kcall;
r = tmp1(kernel, 45U, c);
```

while a source-level call to the same function is direct. `anf_expr` hoists
any operand that is not pure, and the rule had labelled the node that
*names* the function with the function's own effect -- reasonably, since
that is the effect the application has.

`EQual`, `EVar`, `EConst` and `EAny` denote without evaluating. There is
nothing for a binding to sequence, whatever the effect on the node says, so
they are no longer hoisted. Cosmetic for a C compiler; not cosmetic for
generated device code a human is expected to read.

## 36.5 Not fixed

`__global__` on a kernel is now expressible, and the reporter's remaining
blockers are unchanged: the float widths dropped from `KrmlAst.width`
(round 33's gap 1, which also stops their existing plugin building),
`ESizeof`, `TExtern of string & list cty`, and `--custard_unit` and
`--custard_link` being OCaml-only.

Closing a lambda stays the rule's job. Custard could compute free variables
and prepend them, but the parameter order, which captures are values and
which are addresses, and what the runtime entry point expects of them are
all decisions about a calling convention Custard does not define. Guessing
them would produce a kernel that compiles and is wrong.

# 37 The gate's own blind spot

Round 41 of the EverParse trial is the reporter checking section 35.2's
checker the way section 35.2 asks things to be checked: not by watching it
pass, but by constructing the case it should catch.

## 37.1 A cast ends in a closing parenthesis too

`checkgroup.py` skips a `(` whose preceding character is `)`, because that is
a call through an expression and its argument list is C's syntax rather than
a grouping: `(*fp)((x))` is one grouped argument, not two pairs.

A **cast** also ends in `)`, and what follows a cast is its operand, where a
parenthesis *is* grouping. So the rule skipped it:

```c
void p(void){ int q = ((5));       }   /* reported            */
void k(void){ int m = (int)((5));  }   /* silent              */
```

The same pair, one character of context apart. And it is not a hypothetical
shape: it is the third of the three real findings the checker was written
after, the fill loop's bound.

```c
for (size_t i = 0; i < (size_t)(((size_t)1ULL)); i++)
```

Put verbatim into a file with the other two, the checker reported the
`if (!((...)))` and the `malloc((((size_t)1ULL)) * ...)` and said nothing
about the `for`. **It would not have caught a recurrence of one of the three
bugs it exists to prevent** -- which is M10αο's failure one level up, a check
that reads like it covers the class and covers two thirds of it.

The fix is to look *inside* the preceding group rather than only at its last
character. If the content is type-ish -- optional `const`, `unsigned`,
`struct` and the rest, a name, any number of stars -- the group is a cast and
the parenthesis after it is grouping. Anything else is a call through an
expression and its argument list is syntax.

Calibration, so this is not oversold: the reporter searched the real output
for the shape and found **zero** live instances -- no `)((` at all in
`CBORDet.c` or the four CDDL units -- and the cast-aware matcher finds
nothing the old one did not over 8 files and ~600 KB. This was a hole in the
gate and not a bug in the output. It matters because catching the next one is
the gate's whole job.

`checkgroup.py --self-test` is the gate's own gate, and runs with the suite.
It carries the three real findings, the two synthetic shapes above, and the
cases the `)` rule exists for -- a call through a pointer, a call, `(a) &&
(b)`, a cast with a non-redundant operand, and parentheses inside a comment
and a string literal. A matcher that quietly stops recognizing one of its
shapes is exactly the thing this round found.

## 37.2 What the round confirmed

Four measurements, all from the reporter, none needing a change here.

**M10αζ's three were live bugs downstream**, not just in this suite. The
`if (!((...)))` shape was in every CDDL unit and had been for two rounds --
six occurrences per unit, eight in `signoutputargs`. No compiler said
anything about any of them: they are `!` and `&&`, not the `==` that
`-Wparentheses-equality` looks at, so clang was as silent as gcc, which is
M10αξ's point demonstrated on real output. The fix is provably syntax-only
against round 40: every changed line is a parenthesis.

**Warning 377 lands on exactly the types the trial had to spell.** On the
CBOR unit it fires twice, naming the two of the reporter's four shim
typedefs that had no source-level name -- the count and the identities both
match. On the CDDL units it names `Pulse_Lib_Slice_slice__uint8` and the
result option, and their behavioural driver has hardcoded both since round
36. It is not describing a hypothetical consumer; it found the one that has
been in the trial the whole time, without being told.

**M10αο's two new guards were broken rather than observed.**
`make check-settings FLAGS_NoSuchTest=x` fails as it should, and a `CGREP_`
set to an absent string fails once the stamp is removed -- which is the right
way to check an assertion, since one that does not run is worse than none.

**The first full CDDL behavioural re-run since round 36.** Because the
parenthesis fix touched loop exit tests a diff was not enough, so the three
typed drivers were rebuilt and the whole corpus re-run: 12,110 vectors per
entry point, all three identical to the round-36 golden. CBOR direct-to-C
identical, CBOR through karamel to Rust byte-identical, COSE interop signs
and verifies with `--custard_c_no_prefix` output substituted in.

Section 12.11's `Lemma13` is unchanged, and still passes at
`--z3rlimit_factor 4`.

# 38 Floating point

The largest of round 33's gaps, and the one whose answer was least in doubt.
`TInt of signedness & width` had no float, so a float add went through a
`custard_extern` and stayed an opaque call where `u32` got `+`. There was no
design question here: F* already has the source types, karamel already has
the widths, and C has had them since 1972.

## 38.1 The source types

`FStar.Float32` and `FStar.Float64` are shaped exactly like the
machine-integer modules: an opaque `new val t : Type0`, an assumed
arithmetic and comparison vocabulary, and two ways to make a value. The
builtin rules follow `FStarC.Extraction.Krml`'s naming for the same reason
the integer ones do -- karamel is a backend that has to give these a C
meaning, and a discrepancy would be a miscompilation rather than an error.

| source | IR |
| --- | --- |
| `t` | `TFloat Float32`, `TFloat Float64` |
| `add`, `sub`, `mul`, `div` | `EOp` at `PFloat` |
| `lt`, `lte` | `EOp`, result `bool` |
| `ieee_eq` | `Eq` |
| `of_int` | `ECast` to the float type |
| `of_literal "3.14"` | `CFloat ("3.14", Float64)` |
| `bit_eq`, `to_string`, `of_string` | external |

`bit_eq` is deliberately not an operator. It distinguishes the two zeros and
makes a NaN equal to itself, which no C comparison does, so it stays a call
into the support library -- the same choice karamel's `mk_op` makes.
`zero` and `one` need no rule at all: they are `inline_for_extraction let
zero = of_int 0L` and unfold to something that does.

## 38.2 A width that is not an integer width

`prim_op`'s width field was `po_int : option (signedness & width)`, and most
of its readers only ask "is there a width here". A few do not, and those are
the ones a float must not be swept into: `And`, `Or` and `Not` are the
*bitwise* operators at a width and the connectives without one, and a
modular operation at a narrow integer width needs its result truncating,
because C promotes `uint8_t` to `int` before it operates on it.

So the field is now `po_ty : option prim_ty` with `prim_ty = PInt … |
PFloat …`, and the sites that mean "integer" say so through `at_int_width`.
This is a breaking change to the plugin surface, which is why it is a rename
and not a second optional field: a rule that builds a `prim_op` has to be
edited either way, and one that has two optional fields where at most one may
be set is an invitation.

## 38.3 A literal is text

`of_literal` takes a string, and nothing here rounds it: the rounding is the
target compiler's and it happens once. Section 39.2 is how the value is
carried between the two -- exactly, as the rational the decimal denotes --
and the grammar it is read with is the conservative one
`FStarC.Extraction.Krml.valid_float_literal` uses: an optional sign, a
mantissa with at least one digit on one side of an optional point, and an
optional decimal exponent. Anything else is **error 380**, which is the
difference between a diagnostic and `1.0); abort(); (` appearing in
somebody's C. `tests/custard/FloatLit.fst` is that literal.

In C the text carries the suffix its width needs. An unsuffixed float literal
is a `double`, so `1.5f + 2.25f` written without suffixes would be computed
at double precision and rounded once at the end -- a different answer, and
the sort that shows up only at the edges. No cast, because a cast cannot give
a literal its own type and the suffix already has.

## 38.4 What each backend does with it

**C.** `float` and `double`; the operators are C's own at that type, and
`truncate` does nothing, since C does not promote a `float` to a `double` to
add it. `of_int` is a cast, and it is a real one: it rounds above 2^53 at
`Float64` and above 2^24 at `Float32`, which is why it is `ECast` and not
`ECoerce`.

**krml.** karamel's `width` already had `Float32` and `Float64`, so
`krml_fwidth` is a rename and the operators go through the same path the
integer ones do.

**OCaml.** `Float64` is OCaml's `float` and the operators are OCaml's own
(`+.`, `<`, `=`), which is both faithful and better than routing them through
a support module that would only rename them. `Float32` is **refused**, with
error 368: OCaml's `float` is IEEE 754 binary64, there is no binary32 to
round to, and a single-precision program compiled that way would silently
compute at double precision. A backend that cannot round right should say so
rather than round wrong. `tests/custard/FloatSingle.fst` pins the message.

## 38.5 Not fixed

`Float16` and `BFloat16`, which round 33 asked for alongside these two, are
not here and are not one line more work than these were. There is no
`FStar.Float16` to extract *from*, karamel's `width` has no constructor for
them, and C has no standard spelling for either -- `_Float16` is a C23
extension that clang and recent gcc implement on some targets, and `__half`
in CUDA is a library type with no operators of its own. Each of those is a
decision, and none of them is Custard's alone to take.

The shape of the answer is clear enough to write down: a `ulib` module in the
shape of `FStar.Float32`, a `TFloat Float16` beside the two that exist, and a
backend spelling per target. What is missing is the source module and the
agreement about the C spelling, not the IR.

## 38.6 A karamel bug, found on the way

`tests/custard/FloatsKrml.fst` computes with variables where
`tests/custard/Floats.fst` computes with literals, and that is not a matter
of taste. karamel's constant folder reads the operands of a `Mult`, `Div` or
`Mod` at `TInt w` with `Z.of_string` before it checks that `w` is an integer
width -- `Add` has that guard and the other three do not -- so
`F64.div (F64.of_literal "1.0") (F64.of_literal "4.0")` ends the run with
`Invalid_argument("Z.of_substring_base: invalid digit")`.

The neighbouring rewrites are wrong in the same place rather than loud:
`0 * x` becomes `0` and `0 + x` becomes `x` whatever the width, and neither
holds of a float, where `0.0 * nan` is `nan` and `0.0 + (-0.0)` is `0.0`.
`of_literal "0"` satisfies the grammar of section 38.3, so those are
reachable and not just latent.

This is karamel's to fix and the fix is the `is_int` guard that `Add`
already has, plus restricting the identity rewrites to integer widths.
Until then the krml test avoids the shapes that reach it, which is why every
operand in it is a variable. Custard's own C backend folds nothing and is
not affected.

Two smaller ones, not worked around because they are not wrong: karamel
emits a float constant as `(double)3.14159` rather than with a suffix, which
for `Float32` means the decimal is rounded to binary64 and then to binary32,
and a double rounding is not always the same as the single one it stands in
for.

# 39 Literals are values, not text

`CInt of string & option (signedness & width)`. The string was the source
spelling, carried through the whole pipeline and printed back out, which is
the shape the ML extraction has and the shape karamel has, and which the F*
compiler itself abandoned: `Const_int` is `int & int_base` and `Const_real`
is an `FStarC.Real.real`. Custard now agrees with the compiler rather than
with the backends.

## 39.1 An integer is a number and a base

`CInt of int & int_base & option (signedness & width)`: the mathematical
integer it denotes, and the base it was written in. The base is not part of
the value -- it is there because someone wrote `0xff` and should not be shown
`255` in the generated C -- and that is exactly why it must not be part of
equality either. `const_eq` compares the value and the width and ignores the
base, and `Simplify`'s match-against-a-known-constant uses it.

What the text representation cost, in order of how quietly:

- `PrintC.is_one`, which decides whether a `BufCreate` is Pulse's `let mut`
  and can therefore be a plain local rather than a heap allocation, was
  `EConst (CInt ("1", _))`. A one written `0x1` is a one, and got an
  allocation.
- `int_literal`'s `INT64_MIN` special case, which exists because C has no
  negative literals and `-9223372036854775808` overflows before the minus
  applies, was a comparison against the 20 characters of that number in
  decimal. Any other spelling of it wrote a literal a conforming compiler
  must diagnose.
- Every construction site had to render a number to build one. `size_lit
  "1"`, `CInt (show arity, None)`, and in the rule plugin a `BU.int_of_string`
  reading back what `show` had just written.
- A `CInt` could hold a string that is not a number at all, and nothing in
  the type said otherwise.

None of these is a bug anyone reported. All of them are the same bug, which
is that a literal was being compared and pattern-matched in a representation
chosen for printing.

## 39.2 A float is a real and a sign

`CFloat of float_lit & fwidth`, where `float_lit` is a `bool` and an
`FStarC.Real.real` -- the exact rational `mantissa * 10^exponent`, canonical,
so that two literals are equal exactly when they denote the same number.

The sign is separate, and it has to be. IEEE 754 is sign-and-magnitude:
`-0.0` and `0.0` are different floats, `FStar.Float64.bit_eq` can tell them
apart, and `1.0 / -0.0` is negative infinity where `1.0 / 0.0` is positive.
They are the *same real number*, though, and `Real.mk 0 e` is `0` whichever
sign it was given, so a sign folded into the magnitude is a sign lost. This
is the one place where a canonical rational is not enough to say what a float
literal is, and the cost of saying it is a bool.

Nothing else was lost. `real` is exact and unbounded, so no digit is dropped
and nothing is rounded here -- rounding is still the target compiler's job,
done once. `1.5e-3`, `0.0015` and `+15e-4` are one `float_lit` and come out
as `0.0015`, which is what canonical means. What `real` cannot represent --
an infinity, a NaN -- is what `of_literal`'s grammar does not accept either,
so the parser and the representation refuse exactly the same things.

`float_lit_of_string` is that grammar, and it replaces
`valid_float_literal`: a predicate that says text is well-formed and a
function that turns text into a value are the same walk, and having only the
second means there is no way to accept a literal without also knowing what it
is. Error 380 is now "the parse failed" rather than a second opinion.

Printing back is `float_lit_to_string`. `Real.to_string` writes the number
out in full, which is right for `0.0015` and 301 characters for `1e300`,
because `Real.mk` normalizes a non-negative exponent away by multiplying it
into the mantissa. Dividing the zeros back out costs a loop and buys `1e300`
back, and both spellings denote the same rational exactly; the length at
which it switches is a matter of taste and no real literal is near it.

## 39.3 What this does not change

The generated code, except where it was wrong. An integer literal still comes
out in the base it was written in, still with the width's suffix and the
narrowing cast that section 14 put there. A float literal still comes out
with `f` after it at `Float32`. `tests/custard/LitBase.fst` pins all of
that, and pins `-0.0` staying negative, and pins the three spellings of
`0.0015` becoming one.

The krml backend spells the value again, because karamel's `EConstant`
carries text. This section originally said it went out in decimal always, on
the grounds that a base is not something karamel's reader of these expects.
That was wrong, and section 43.2 replaces it: karamel does pass the text
through, so the base is kept wherever the far end reads it back unchanged.

# 40 Half and bfloat16 without a compiler change

Section 38.5 left `Float16` and `BFloat16` out, on the grounds that the
missing half is not the IR: it is a `ulib` module to extract *from* and a C
spelling to extract *to*, and both of those are facts about a target rather
than about F\*. That is an argument for not guessing in the compiler. It is
not an argument for waiting, because a program that *has* a target can supply
both itself, today, with nothing added to Custard.

`tests/custard/Half.fst` is that program, written against the shape of
nvcc's `<cuda_fp16.h>` and `<cuda_bf16.h>`:

```
[@@custard_extern "__half"; custard_c_header "Half_stubs.h"]
assume val half : Type0

[@@custard_extern "__hadd"; custard_c_header "Half_stubs.h"]
assume val hadd (x y : half) : half
```

The external-type facility of section 14.5 already does the whole of it. No
typedef is emitted for `__half` or `__nv_bfloat16`, the header is included,
and the C names in the attributes are the ones that appear. `__float2half`
and `__half2float` sit next to `FStar.Float32`, which is a real `float` now,
so the conversions are the ones CUDA declares rather than a rounding Custard
invented.

Two things make this more than a spelling. Arithmetic on CUDA's half types is
*functions* in C -- `__hadd`, `__hmul`, `__hlt`; the operator overloads are
C++ only -- so an external declaration is not a workaround here, it is the
faithful translation, and it is what section 38.1 chose for `bit_eq` for the
same reason. And the types are ordinary F\* types, so the rest of the
pipeline treats them as such: `Half.fst` passes `hadd` to a polymorphic
`twice`, which monomorphization specializes into `Half_twice__half` and
`Half_twice__bfloat16`, and stores both in a record, which the layout
analysis lays out as a struct of a `__half` and a `__nv_bfloat16`.

What a program written this way does *not* get is what section 38 gave
`Float32`: a literal, and `+` instead of a call. A half literal has to be
`__float2half` of a `float` one, which is a conversion at runtime unless the
C compiler folds it, and there is no `EOp` at a half width, so nothing in
`Simplify` knows that `__hadd` is associative or that adding zero does
nothing. For a kernel whose arithmetic is intrinsics anyway that is no loss;
for one that wanted `a + b` it is the reason `TFloat Float16` would still be
worth having, once there is a `ulib` module and an agreement about what
`__half` is called on a target that is not NVIDIA's.

Round 43 compiled this against the real `<cuda_fp16.h>` and `<cuda_bf16.h>`
under `nvcc`, linked it and ran it. One correction came back: `__hadd_bf`
above is not a CUDA name. Those headers are C++ and overload `__hadd` on the
operand type, so the two additions name *one* C symbol -- which needs nothing
from Custard, since monomorphization gives each `val` its own specialization
and overload resolution picks from there. The test keeps the invented name;
see section 43.4 for why C11 cannot host the real one.

The stub header exists so the test runs under `gcc`. Nothing on the F\* side
would differ under `nvcc`.

# 41 Round 42's two reports

Both reports were largely confirmations -- CUDA compiled by `nvcc`, EverParse
byte-identical -- so this section is about the four things that were not
already true.

## 41.1 The blit

Section 35.2 routed every parenthesized operand of the C printer through
`group`, which parenthesizes only what is not already a group. One site did
not get routed: the `BufBlit` case's length,

```
    ", (" ^ lenv ^ ") * sizeof(" ^ elt ^ "));\n"
```

which is the hand-written pair `group` exists to replace, and which the two
neighbouring length positions in the same case do not have. It is the last
`"(" ^ <a printed expression> ^ ")"` in the file; the three other hits of
that shape are argument lists, where the parentheses are syntax.

The reason the sweep missed it is that nothing had ever printed it.
`Pulse.Lib.ArrayPtr.memcpy` is the only rule that produces a `BufBlit`, and
no test in either directory called it. `tests/custard/pulse/PulseBlit.fst`
does, and section 32.10's gate reported the bug on the first run rather than
anyone having to look for it -- which is the second time the gate has found
something the sweep that installed it did not.

It bites when the length is *already* a group: a literal, a cast, an
arithmetic expression. EverParse's one real `memmove` passes `src.len`,
which is not, so `group` produces the same `(src.len)` the hand-written pair
did and every EverParse output is byte-identical with the fix in. One
unreached printer site, zero live instances -- reported that way, and checked
before it was reported that way.

## 41.2 A self-test that tested the wrong bug

Section 37's `--self-test` was mutation-tested: fourteen decision branches of
`checkgroup.py` flipped one at a time, six survived. The one that matters:

```python
CHECKED_KEYWORDS = frozenset()      # was {'if','while','switch','return','do'}
```

survives, so the gate goes blind to `if ((cond))`, `while ((cond))` and
`return ((x))` -- which is **section 32.10's bug, the one the matcher was
written for** -- and the self-test says nothing.

The reason is structural rather than an oversight about one case. Every
positive case in `SELF_TEST` had its redundant group behind `!`, `=`, `(` or
a cast, because every one of them was a round-41 finding and round 41 was
about casts. `CHECKED_KEYWORDS` was therefore never read on a path that
decided an expected outcome. A faithful regression test for the bug it was
written for, with no opinion about the bug the file exists for: the same
failure one level down from the one section 37 fixed.

Six cases close four of the six gaps -- the three keyword shapes, a call
through an array of function pointers (`]` is syntax too), and the two
literal skips, one of which needs the backslash escape to find the end of the
string. The remaining two mutants are *equivalent*, which was checked and not
assumed: `inner.endswith(')')` is subsumed by the emptiness test that
follows it, and the unmatched-open fallback is reachable only from a file
with unbalanced parentheses. Over 659 KB of real output both produce
byte-identical findings.

## 41.3 The keyword set is complete, and the argument is about the printer

Round 41 left three shapes the matcher does not check -- `sizeof((5))`,
`case ((1)):`, `else ((p));` -- each behind an identifier not in
`CHECKED_KEYWORDS`. Grepping the output would only say they do not occur
today. The printer says they cannot:

- `sizeof(` is emitted at two sites, both `sizeof(" ^ elt ^ ")`, always a
  *type*, where the parentheses are mandatory and reading them as a call is
  correct;
- `else` is emitted at three sites, always followed by `if (` or a brace,
  never by a parenthesized expression;
- `switch` and `case` are not emitted at all -- they appear only in the
  reserved-word list.

So the keyword set is complete with respect to what this printer can produce,
and would need extending exactly when `switch` starts being emitted. That is
the right form of the argument for a gate on generated code: not "the corpus
has none of these" but "the generator cannot write one".

## 41.4 What nvcc said

Section 36 was built and argued for without an `nvcc`. There is one now, and
three of its answers are worth keeping.

**`Prologue "__global__"` on the prototype as well as the definition was
load-bearing, not defensive.** The argument for putting a flag on both was
that a qualifier on one and not the other "is a redeclaration error, which is
a much better failure than a silently host-side kernel". It is precisely
that:

```
proto_only.cu(4): error: a __host__ function("kern") redeclared with __global__
```

Had the flag gone on the definition only, *every* generated kernel would have
failed to compile. The choice was between a hard stop and a working program,
not between a hard stop and a subtle bug.

**The output is a kernel, not C that looks like one.** `nvcc -ptx` gives
`.entry _Z6kernelj`, and `cuobjdump -symbols` gives `STO_ENTRY`, which is the
linker saying the symbol is launchable. `nvcc -std=c++14 -c` and
`nvcc -Xcompiler "-Wall,-Wextra,-Werror"` both exit 0.

**`lift_named`'s guarantee is about the C source, and `nvcc` compiles as
C++.** So `kernel` is `_Z6kernelj` in the object file. Profilers demangle, so
`nsys` shows `kernel(unsigned int)` and the guarantee holds where a human
reads it; what it does not survive is a lookup *by string* --
`cudaGetSymbolAddress`, or a launcher taking a name rather than a symbol. A
program doing either needs `extern "C"`, which is a `Prologue` away and is
not something Custard should decide.

For the record, the name is the point of the exercise: the same kernel
through the existing Krml plugin is `__hoisted_reduce_u32_0`.

## 41.5 Gap 1, checked

Round 33's gap 1 has been reported five times as "float widths dropped from
`KrmlAst.width`", most recently as the thing that stops an existing karamel
plugin building against upstream at all. It is worth writing down that this
is not what upstream looks like, because it changes what the fix is.

`FStarC.Extraction.KrmlAst.width` has `Float32 | Float64` and has for some
time. So does karamel's `Constant.width`. So does
karamel's `InputConstant.width`, which is the one that matters, since it is
the wire type of the `.krml` file and the two ends are marshalled
positionally -- and it carries the `Bool` width that the internal type does
not, for exactly that reason, with a comment saying so. Section 38's krml
backend went through all of this end to end (`tests/custard/FloatsKrml.fst`)
before this was checked, which is the evidence that the ABI is intact.

What is genuinely absent everywhere is `Float16` and `BFloat16`, in F\*, in
`KrmlAst`, in `InputConstant` and in `Constant`. Section 40 is what a program
that needs them can do today; section 38.5 is what adding them would take.

# 42 Separate compilation for C

§33.5 and §34.4 both recorded the same thing: `--custard_unit` and
`--custard_link` were implemented for the OCaml backend only, and that was the
largest thing the reports left open. Kuiper ships 62 generated `.cu` files and
cannot treat whole-program-per-kernel as a workaround.

None of §12.1–12.6 changes. The `.cui` format, the specialization key,
`Extract.request`'s third answer, the acyclicity argument and the reason
freezing the layouts is sound are all statements about the IR, and the IR does
not know which backend will print it. What was missing was entirely a *C*
question, and it is four questions, not one.

## 42.1 What a C unit offers: the linking interface, and nothing else

The decision that makes the rest fall out: **a C unit's `.cui` describes its
linking interface**, so it exports what the header file declares and nothing
that the header file does not.

That is a real narrowing against OCaml, which exports every declaration a
request created (`Extract.exported_keys` is `st.names`, the whole table). It
has to be. `PrintC.is_public` marks a declaration `static` unless it is a
`Root`, and the comment there defends that hard: without it a whole-program C
file exports every definition it happens to contain, so linking two of them
together is a symbol collision, and nothing can be inlined across a call by a
compiler that must assume some other unit might call it. Offering a `static`
definition in an interface would be offering a downstream unit a symbol it
cannot name. OCaml has no such problem because every definition in a module is
nameable from outside it, so there the two sets coincide by accident of the
module system rather than by design.

So `Driver.unit_entries` gains one filter under `--custard_backend C`: a
`DLet` that is not `is_public` is dropped. `DType` is kept — every one of
them, not merely those a public signature mentions, because that is exactly
what the header already contains and for the reason already written there: a
`struct` or a `typedef` has no linkage, so there is nothing to hide from the
linker, and trimming buys an incomplete header and a class of "field has
incomplete type" errors. `DExternal` was already excluded, for the reason in
§12.2: an external is a hole a unit *leaves*, not a symbol it provides.

**This removes the need for §12.7's per-unit symbol prefix**, which was the
one design note §12 left as a sentence. Statics cannot clash, whatever they
are called. What is left with external linkage is the roots, and a root exists
because `--custard_entry` named it. Two units can still collide, by both being
told to export the same definition and then being linked together without one
linking the other — but that is a user telling two units to own one symbol,
the linker's message says so, and a prefix would paper over it rather than fix
it. The prefix can come back the day something needs it; §12.3 says the names
need not be deterministic, so it was never going to be free.

The cost is that a downstream unit re-specializes anything the upstream kept
private, and compiles its own `static` copy. Duplication, not a clash — and
§12.6 already says separate compilation deduplicates nothing it was not told
about.

## 42.2 Headers include headers

The upstream unit's header *is* the downstream unit's view of it, so the
downstream unit `#include`s it and does not re-declare anything. Re-declaring
is not a stylistic alternative: §14.10 is the record of what happens when the
direct backend writes a prototype of its own making, `extern custard_unit
EverCrypt_AutoConfig2_init(custard_unit)`, against a definition that was
declared otherwise. It compiles, and it is wrong.

So an imported declaration is skipped at every emission site — no forward
declaration, no `typedef`, no `struct` body, no prototype, no definition, no
global initializer — while still being handed to the printer exactly as it is
today, because the tables it builds (the type table, the constructor table,
the arity table, the unit-parameter and `void`-result tables, and
`build_renames`) all have to see an import or a later pass will make a
decision about it that its home unit already made differently. That is the
same split §12.4 rule 2 describes for the middle of the pipeline: present so
that this unit's passes can see its shape, absent from what is emitted.

The header file to include is recorded in the `.cui` rather than derived from
the unit's name, because `-o` decides the name and the interface is written
before that is a settled question in only one place.

**Types therefore stop being a problem, and this is the reason to export all
of them.** A header carries the whole type language, so if two units both
reached `(uint32_t & uint32_t)` and both defined its tuple `struct`, a
translation unit including both headers would see the same `struct` defined
twice, which is an error in C and in C++ alike. Because every `DType` is in
the `.cui`, the downstream unit's request for that tuple resolves through the
link and it emits nothing. The alternative — wrapping each generated type in
an `#ifndef` guard on its own name — would have been wrong, and instructively
so: §12.3 says names are *not* deterministic, so two units can give one name
to two different types, and a name-keyed guard would silently keep the first
and misinterpret every value of the second.

One thing does stay duplicated, and gets a guard for exactly the reason the
generated types could not:

```c
#ifndef CUSTARD_UNIT_DEFINED
#define CUSTARD_UNIT_DEFINED
typedef uint8_t custard_unit;
#endif
```

`custard_unit` is a fixed name for a fixed type that this compiler chose once
(§5.1). Two spellings of it are the same spelling, so the guard cannot hide a
conflict. It is emitted unconditionally, not only under `--custard_unit`, so
that a hand-written file may include two independently generated headers.

## 42.3 The initializer is namespaced, and someone has to call it

A unit with globals emits `custard_init_globals`, one fixed name per unit, and
two of those in one link is a duplicate symbol. Under `--custard_unit U` it
becomes `U_init_globals`; with no unit name the old spelling is kept, so every
existing whole-program output is unchanged.

Renaming it raises the question the whole-program case never had to answer:
who calls it. The unit holding the `Entrypoint` emits `main`, and `main` calls
each linked unit's initializer, in `--custard_link` order, before its own. The
`.cui` records the initializer's name, and absence of a name is how a
consumer knows a unit has no globals and there is nothing to call — the same
convention the whole-program header already uses, where the prototype is
emitted when there is anything to do and omitted otherwise.

`--custard_link` order is the user's order and need not be a topological one,
so the initializer body gets a re-entry guard under `--custard_unit`:

```c
void U_init_globals(void) {
  static bool custard_initialized = false;
  if (custard_initialized) return;
  custard_initialized = true;
  ...
```

which makes calling it twice harmless and makes a unit free to call its own
dependencies' initializers later, if it ever needs to. The guard is not
emitted in whole-program mode: there is exactly one caller there and the
branch would be noise in output meant to be read.

## 42.4 Two fields, and a version bump

`Unit.header` grows `uh_header` and `uh_init`, both `option string` and both
`None` for an OCaml unit, and `Unit.current_version` is bumped. A `.cui` is
read with `Util.load_value_from_file`, which is positional, so this is not a
compatible change and is not meant to be one — the version check exists so
that a stale interface is an error rather than a miscompilation.

## 42.5 What the MVP does not do

- **No re-export.** A unit's `.cui` lists what that unit emitted, so if `C`
  uses something `A` compiled and `B` merely passed through, `C` links both
  `A.cui` and `B.cui`. This is the ordinary C situation — you pass the linker
  all the objects — and it is what §12.6's "a unit is whatever was reachable
  and not already in a linked interface" already implied.
- **No symbol prefix**, per §42.1.
- **No output splitting.** §12.9 is an OCaml problem: it exists because
  hand-written OCaml realizations reference modules Custard compiles, and C
  has no realizations and no DAG requirement on translation units.
- **The karamel backend still refuses.** karamel does its own bundling and
  has its own opinion about what a compilation unit is; wiring `.cui` into it
  would be answering a question that has not been asked.

`tests/custard/SepLibC.fst` and `SepAppC.fst` are the test, and they check
with `nm` what the compiler cannot: that the exported root has external
linkage under its own name, that the private helper does not appear in the
symbol table of either object, and that the library's definitions appear in
exactly one of the two.

# 43 Writing a number down

Round 43 found three ways to spell a number that the target reads back as a
different number, or as nothing at all.  All three had the same shape: the IR
carries the literal as *text*, and text is only as portable as the reader on
the far end.

## 43.1 C does not spell octal the way F* does

`Syntax.int_lit_to_string` was `FStarC.Const.string_of_int_literal`, which
spells a literal the way F* source does: `0x`, `0o`, `0b`, or bare.  Two of
those four are F*-specific.  No C compiler accepts `0o17` -- gcc reports
`invalid suffix "o17U" on integer constant` -- and `0b1010` is a GNU extension
that C did not standardize until C23, so it warns under `-pedantic`.

`Syntax.c_int_lit_to_string` is the C spelling: octal is respelled with C's
leading zero, binary falls back to decimal, hex and decimal are unchanged
because F* and C agree on those two.  `PrintC.int_literal` uses it; nothing
else does.  In particular the diagnostic at the unbounded-literal rejection
still uses `int_lit_to_string`, because that message quotes the *source*, and
the source is F*.

A base is a courtesy to the reader.  The value is not negotiable.  When the
target cannot write a base, the base is what gives way -- `0b1010` becomes
`10` and nothing is lost but the hint.  Octal is the one case where the base
can be preserved, because C has a spelling for it; it is just not F*'s.

`LitBase` had covered exactly the two bases whose F* and C spellings coincide,
which is why it could not see this.  A test that only exercises the cases
where two languages agree is testing the agreement, not the translation.

## 43.2 The karamel path had dropped the base entirely

All four sites in `PrintKrml` that spell an integer -- the two `CInt` cases in
`krml_const` and the two in `krml_pat` -- did `show v`, i.e. decimal, always.
§39.1 had recorded this as deliberate.  It was wrong: for a Rust consumer this
regressed the one place where a base carries meaning, a UTF-8 validator whose
byte ranges read `0x7fu8` before and `127u8` after.

`PrintKrml.krml_int_lit` restores it, but not uniformly, and the asymmetry is
the interesting part:

- **`KrmlRust` gets every base.** Rust spells `0x`, `0o` and `0b` exactly as
  F* does, and karamel's Rust backend puts the text through very nearly
  verbatim.
- **`KrmlC` gets hexadecimal, or decimal.** Not octal, even though C has a
  spelling for it and §43.1 just used it.

The reason for the second is a trap worth recording.  karamel does *not* treat
the constant text as opaque everywhere; some path on the way to C parses it,
and parses it as decimal.  A leading-zero octal `017` therefore comes back out
as **seventeen**, silently: valid C, wrong number.  Hexadecimal survives the
same trip unchanged, which is what makes the failure so easy to miss -- the
one base a C author would think to test is the one that works.

This is also a lesson about what to assert.  A `CGREP` on the spelling would
have passed: `017U` is exactly what one would grep for, and `017U` is exactly
what came out.  Only a test that computes with the constant and checks its own
answer can see a number that changed.  Every assertion in `LitOct` is of that
kind: `main` compares each value against its decimal and returns *which one*
was wrong.

## 43.3 A binary32 literal needs its suffix

karamel's C printer attaches a suffix per width (`karamel/lib/PrintC.ml:245`),
and the table has no float case, so a `Float32` constant goes out bare.  A
bare decimal in C is a `double`.  karamel then inserts the `(float)` cast that
makes the *type* right, and the cast is exactly what makes the *value* wrong:
decimal to binary64 to binary32 is a double rounding, and for some decimals
the two roundings disagree by one ulp.

`7.038531e-26` is such a decimal.  Correctly rounded to binary32 it is
`0x15ae43fd`; routed through binary64 first it is `0x15ae43fe`.

`PrintKrml.krml_float_lit` writes the `f` into the constant text at `Float32`,
so the literal is a `float` before the cast ever sees it and the cast becomes
the no-op it was meant to be.  Confirmed end to end: karamel emits
`(float)0.000...07038531f` and the program agrees with the exact value.  Not
on the Rust path, where the suffix is `f32` and karamel writes it itself, and
not at `Float64`, where bare is already right.

This is a workaround for something upstream: a one-line `| Float32 -> string
"f"` in karamel's suffix table would fix it at the source.  Should that
land, this must be removed on the same day, or the output becomes `1.5ff`.
The direct C backend has always written the suffix, and `LitF32` now runs on
both backends so that the two cannot drift apart again.

## 43.4 Round 43's other findings

Kuiper **withdrew gap 1**.  The build failure was `Identifier not found:
Float16`, not a missing `Float32`/`Float64`: §41.5's statement was already the
correct one, and `Float16`/`BFloat16` exist nowhere, upstream included.  His
words: no `Float16` in the IR, please.  §40's route -- an opaque extern type
plus `custard_extern` intrinsics -- stands, and it was validated against the
real `<cuda_fp16.h>` and `<cuda_bf16.h>` under `nvcc`, compiled, linked, and
run.  Two things came out of that:

- **Two `val`s may carry the same `custard_extern` target.** CUDA overloads
  `__hadd` on operand type rather than offering `__hadd_bf`, so the half and
  bfloat16 additions name one C++ symbol.  Monomorphization gives each F*
  `val` its own specialization and C++ overload resolution then picks by
  argument type, so this works without Custard knowing anything about it.
  §40's `__hadd_bf` was an invention; the mechanism was right anyway.
  `Half.fst` keeps the invented name, because its stub header is compiled by
  a C11 compiler, C has no overloading, and `twice hadd` passes the extern as
  a *function pointer*, which a `_Generic` macro cannot be.  Against the real
  headers, which are C++, both `val`s would say `__hadd`.
- **`EOp (Lt, Float16)` is a latent bug in the consumer, not a gap here.**
  `operator<` on `__half` is guarded by `#if !defined(__CUDA_NO_HALF_-`
  `OPERATORS__)` and is C++-only; it does not exist in CUDA C.  `__hlt` is
  unconditional and is what an extern should name.  A comparison is not more
  primitive than an addition just because it has an infix spelling.

Of the ten remaining `EConstant (Float16, ...)` uses, every one holds a
snippet of C (`__float2half_rn(0.0f)`) rather than a number -- `EConstant`
used as an escape hatch because there is no half literal.  §40 covers these
as nullary externs, which is what they are.

Still open for him: `ESizeof`; `TExtern of string & list cty`, which he now
narrows to genuinely *indexed* externals like `wmma::fragment<...>` (the
`__half`-shaped cases are already covered by §40's opaque extern types); and
§34.4's "was this attribute read" bit.  `--custard_unit`/`--custard_link` for
C shipped in §42, which he had not seen when he wrote.

`Simplify.ml:462` (`M10ββ`) reproduced in eight lines: karamel's constant
folder guards `Add` with `is_int w` and does not guard `Mult`, `Div` or `Mod`,
so a float multiply reaches an integer path and asserts.  Still upstream's,
still avoided here by not folding at float widths.

# 44 Two ways to not compare

Round 43 was about writing a number down. Round 44 is the same shape one
level up: a *constant* that one backend can express and another cannot, and
what each of them did about it. The three backends disagreed three ways on
one construct -- a `match` on a string. `PrintOCaml` was right, because OCaml
has string patterns. `PrintC` emitted something wrong. `PrintKrml` emitted
something that was not a test at all.

## 44.1 A pattern the backend cannot hold must stop the extraction

karamel's `pattern` has no node for a string, float or character constant.
`krml_pat`'s last case was:

```
| PConst _ -> (extend env "_", K.PVar (dummy_binder "_"))
```

A variable pattern matches *everything*. So the first such branch swallowed
the scrutinee and every branch after it was dead code. A three-way `classify`
on strings became the constant `1`, and karamel then reported the argument
unused, which is the only trace it left:

```
uint32_t PatStr_classify(Prims_string s)
{
  KRML_MAYBE_UNUSED_VAR(s);
  return 1U;
}
```

The Rust backend shows the mechanism without the constant folding on top:
`match s { __ => 1u32, __ => 2u32, _tmp => 3u32, ... }` -- three catch-alls
where there should have been two tests and a default.

The fix is not a better translation, because there is no translation: a
construct the target AST cannot hold has to stop the extraction. `POr` next
door already did that, and `PConst` now does too.

But it does it differently, and the difference is the second half of this
change. The three refusals in `PrintKrml` were `failwith`s, and all three
said **"not supported by the C backend"** -- from the file that is not the C
backend. §33.4's rule about wrong explanations applies to wrong *addresses*
as well: a reader who is told the C backend refused this goes and reads
`PrintC`, where nothing refuses it. `krml_reject` replaces all three with an
`Error_CustardNoCRepresentation` that names karamel, says why (its AST has no
node for this), and says what else to try (`--custard_backend C`, which
accepts all three).

This is the counterpart of §43.2's lesson about assertions.
`KRML_MAYBE_UNUSED_VAR(s)` is a hint that an argument went dead, and nothing
greps for that either. `LitOct` passes through karamel precisely because its
`match` is on integer patterns, which `krml_pat` does handle -- the test that
was written to catch a silent constant did not catch a silent pattern,
because it was made of the one kind of constant that works.

## 44.2 C compares strings by address

`Prims.string` is `const char *`. Two sites emitted `==` on one:
`pat_tests`'s `PConst` case, and the infix-operator case for `Eq`/`Neq`.
Both are comparisons of addresses. F\*'s equality on strings is equality of
contents, and whether two equal strings share an address is a decision the C
compiler makes about its literal pool -- not a fact about the program.

gcc says so unprompted:

```
warning: comparison with string literal results in unspecified behavior [-Waddress]
```

`is_string_ty` decides when a `const char *` is a `Prims.string`, and both
sites now emit `strcmp`, which `<string.h>` -- already unconditionally
included by every generated header -- declares.

The reason this survived is worth more than the fix. **The generated program
exits 0 with the bug in it**, as long as every string it compares is a
literal, because the C compiler pools literals and the two addresses then
agree by accident. A test written the obvious way tests the pool. So
`PatStr.fst` obtains its strings through a `custard_extern` that `malloc`s a
copy: same contents, different address. With the bug restored by hand,
`classify` of a heap `"a"` returns 3 and the test fails; that was checked,
not assumed.

`pat_tests` receives the type of the path it is testing, so it can tell a
string pattern from any other constant pattern without inspecting the
constant -- which is the right way round, since it is the *type* that decides
whether `==` means what F\* meant.

There were zero live instances: EverParse's output contains no
`Prims_string` at all, and no test in either directory matched on a string
constant, which is exactly why all three sites survived this long.

## 44.3 Kuiper builds, and §42.1's asymmetry is why

Round 44 built five real Kuiper kernels as five separate C units, compiled
each under `nvcc` as C++ *and* under `clang -std=c11 -Wall -Wextra -Werror`
as C, linked them into one binary and ran it. No duplicate global symbol
across any of the five, and all five headers coexist in one translation unit
under both compilers.

§42.1 justified restricting a C unit's `.cui` to its linking interface on the
grounds that a `static` is a symbol the consumer cannot name. Kuiper supplies
a sharper reason, and it is worth recording because it changes the argument
from tidiness to soundness. Two of the five units contain:

```
/* KMul.c  */
static uint64_t Kuiper_Array_Core_slice_read__t(uint64_t *r, size_t i);
/* KArr1.c */
static uint32_t Kuiper_Array_Core_slice_read__t(uint32_t *r, size_t i);
```

The same generated name at incompatible types -- one `slice_read`
monomorphized at `u64` in one unit and at `u32` in the other -- and §12.3's
non-determinism means neither unit can know the other exists. Because both
are `static`, C++ mangles them apart and C never sees them together. Had the
`.cui` exported everything a request created, which is what the OCaml backend
does, both headers would declare that name and a consumer of both would not
compile. Kuiper's shared code is almost entirely polymorphic and
`inline_for_extraction`, so across its 62 units this would have been the
common case rather than a corner one.

Two smaller confirmations. The mangling worry from round 42 does not apply at
unit boundaries: the generated header wraps its declarations in `extern "C"`,
so an exported root keeps its C name under `nvcc` and only unit-local statics
are mangled. And §42.1's cost -- a downstream unit compiling its own private
copy of anything upstream kept `static` -- is not a new cost for this
consumer: Kuiper's shipped `dist/` is already 62 `.cu` files, each including
only its own header, with helpers `static` and duplicated (one file alone has
144 `static` definitions). One unit per `.cu` maps onto §42 with no
impedance mismatch, so the round offered on grouping is not needed.

# 45 Naming what is already named

Round 45 arrived as a *withdrawal*. Round 44 had ended with an offer to build
indexed `TExtern` -- `wmma::fragment<matrix_a, 16, 16, 16, __half,
row_major>` -- if the TensorCore GEMM was the last thing blocking a Kuiper
build. It was not. Kuiper never emits that type: its own extraction plugin
declines to, because the indices are erased to unit before it sees them, and
the shipped `dist/` says so plainly -- the fragment type is never *named* in
the generated code. It is `auto&`, inferred from a macro call.

So the feature was not needed. What was needed turned out to be three much
smaller things, all of which are about a name that already exists somewhere
else and Custard's various opinions about it.

## 45.1 A `custard_extern` target is not an F\* name

`PrintC` printed an external's target through `escape_kw (sanitize t)`.
`sanitize` maps every byte outside `[A-Za-z0-9_]` to `_`, which is the right
thing to do to an F\* name that has to become a C identifier -- and exactly
the wrong thing to do here. `wmma::mma_sync` became `wmma__mma_sync`:
sanitizing does not make an illegal identifier legal, it makes an existing
symbol absent.

The external *type* path had been verbatim since §14.5, which is why a
program could get `auto&` in type position and a mangled call on the next
line. The value path now matches it. `escape_kw` stays, because a target
that is a C keyword really is a mistake.

This is not a corner: `wmma::`-qualified names are the *entire* TensorCore
surface, 2,530 references across 9 names in Kuiper's shipped output, and all
of them on the callee side.

The negative control is worth stating, because it is the whole argument for
the fix: substituting the sanitized spelling back into the generated
`TensorC.dc` by hand gives `implicit declaration of function
'TC_NS_mk_a'` and then `invalid initializer`. There is no header in which
that name exists, so nothing downstream can rescue it.

Verbatim raises one question the old spelling hid. Custard emits a prototype
for an external that has no `[@@custard_c_header]`, and a prototype needs a
declarator -- `extern void wmma::mma_sync(...)` is not one. So a target that
is not a C identifier and has no header is now refused, and the message says
which of the two to add. Sanitizing had turned that into a link error a long
way from its cause.

## 45.2 A C decoration written in F\* source reaches the C

`Prologue`, `Epilogue`, `Comment` and `CInline` existed as flags, and both
printers honoured them (§36.3), and nothing in `Extract` ever constructed
one. The only way to attach a decoration was `B.lift_named` from a rule
plugin. For a program with 654 `__global__` kernels that means either a rule
per kernel or a rule that pattern-matches all of them -- to say a thing that
F\* has had an attribute for since karamel did.

`c_decoration_flags` reads `FStar.Attributes`'s `CPrologue`, `CEpilogue`,
`Comment` and `CInline` off the definition. The ML extractor has read them
all along (`FStarC.Extraction.ML.Modul.extract_meta`) and karamel forwards
them, so it was only Custard's side of the join that was missing.

Two details:

- **Both the sigelt's attributes and the letbinding's are read, and the
  result is deduplicated.** F\* records a definition's attributes in both
  places and which one a given attribute lands on is not stable, so reading
  one is unreliable and reading both emits everything twice. Two `__global__`s
  is not a redeclaration error, it is a syntax error.
- **Every specialization of a decorated definition carries the decoration.**
  That is right for `__global__` -- each specialization is its own kernel --
  and it is the only answer available, since the attribute is on the source
  and the source is what was specialized.

Custard does not read the strings. What they mean is a question about the
target.

## 45.3 An external through karamel was declared and never called

`PrintKrml` emitted the `DExternal` under the `[@@custard_extern]` target,
via `x.dx_target`, and every *call site* under the F\* name, via
`lident_of_name`. The result declared one symbol and called another. Nothing
defined the name that was called; nothing called the name that was declared.
Neither karamel nor the C compiler had reason to object, because each half
was well formed on its own -- it is a link error, at best, and it is silent
up to that point.

The type path had had the right mechanism all along: an `extern_types` table
and a `type_lident_of_name` that consults it. `extern_values` and
`value_lident_of_name` are its counterpart, which is the whole fix.

The same path also dropped the `[@@custard_c_header]` include, so even the
right name would have been undeclared. karamel's `Prologue` flag is verbatim
text before a declaration, and an `#include` is verbatim text, so the header
now rides on the `DExternal` and karamel emits it into the generated header
where the prototype is.

The direct C backend was right about all three. This is the second round in
which the three backends disagreed about one construct (§44), and the
pattern is the same both times: the C backend is where the attention has
been, and the krml path silently inherits whatever nobody looked at.

## 45.4 What the withdrawal was worth

The report that withdrew the feature also built the TensorCore kernel with
today's IR and nothing else -- an opaque `custard_extern "auto&"` per
fragment role, a `custard_extern` macro per configuration, and the `wmma::`
entry points as ordinary externs -- and got Kuiper's shape line for line,
compiled it under `nvcc -arch=sm_70`, and found a real
`wmma.mma.sync.aligned.row.row.m16n16k16.f16.f16` in the PTX. The only two
hand-patches it needed were §45.1 and §45.2.

That is a better outcome than the feature would have been, and it is worth
recording why the feature looked necessary: the request was made from
reading a plugin's *intent* rather than its *output*.
`tests/custard/TensorC.fst` is that shape, reduced to what a C11 compiler can
host -- a type whose spelling is not an identifier, and calls whose names are
not identifiers either.

What remains genuinely unknown is whether the per-configuration macro names
can be *generated* from the erased F\* indices. §34.1 gives a rule reduced
arguments, so it may be recoverable there; nobody has tried it yet.

# 46 Two constants and a handler

Round 46 stayed inside the two functions round 45 had edited and asked what
*else* was in them. Both answers were the same shape as round 44's: a
construct the karamel path could not hold, translated into something that
was not a refusal and not the program either.

The recurring finding is worth naming before the cases. Custard has two C
backends, and every bug in this round and the last three is a place where
they disagree about one construct. That is not a coincidence: the direct C
backend is where the attention has been, so it is usually the one that is
right, and the krml path is where a construct quietly means something else.

## 46.1 A character constant is a `uint32_t`

`krml_const`'s `CChar` case was

```fstar
| CChar _ -> K.EAbortS "Custard: character constants are not supported by the C backend"
```

which is wrong in three separate ways, and the third is the one that
matters.

It is not a refusal. `EAbortS` is a *translation*: the program extracts
with no diagnostic, compiles, links, and then aborts when control reaches
the constant. On the Rust backend that is a `panic!` in a Rust binary,
quoting a message about the C backend.

The message names the wrong component. `PrintKrml` is not the C backend.

And the claim is false. The direct C backend has handled character
constants since §6 -- `PrintC.constant` gives `((uint32_t)97)` and
`builtin_type` maps `FStar.Char.char` to `uint32_t`. The sentence told a
reader that the one backend which does support this is the one that does
not.

The representation was never in question. It is `uint32_t` in `PrintC`, it
is `uint32_t` in krmllib's `include/krml/internal/types.h`, and the krml
path was the only place that had not been told. So `prim_type` now says it,
`krml_const` emits `EConstant (UInt32, "97")`, and a character *pattern* --
refused separately, as "a character pattern" -- is now an integer pattern
like any other, because that is what it is once the type is settled.

`ChrLit.fst` checks its own answer rather than grepping for a spelling
(§43.2), and its match is deliberately out of source order:

```fstar
match letter () with
| 'b' -> 1l
| 'a' -> 0l
| _ -> 2l
```

If a character pattern were ever to fall back to a variable pattern -- the
§44.1 failure -- the first branch would swallow the scrutinee and the answer
would be 1.

## 46.2 The type alone did not compile

Found while trying to run §46.1's KrmlC output, and separate from it.

`FStar.Char` is a realized module (§8.2), so `FStar.Char.char` reached
`krml_typ` as an opaque `TQualified` and got an opaque forward declaration:

```c
typedef struct FStar_Char_char_s FStar_Char_char;
```

against krmllib's own `typedef uint32_t FStar_Char_char;`, which every
generated header includes. `error: conflicting types for 'FStar_Char_char'`.

This needs **no character constant**. A function whose only char is a
*parameter* extracts with rc=0 and no diagnostic, and produces a header that
cannot be compiled. `ChrTy.fst` is that program, and it gets its char from a
`custard_extern` precisely so that it contains no literal.

The fix is the same line as §46.1's, which is the point: `krml_decl` already
drops a `DType` whose name has a `prim_type`, because a type the target
defines is not ours to declare. Teaching `prim_type` the representation
retires the declaration for free. No widening of the `KrmlRust`-only
`is_krml_model` gate was needed -- that had looked like the mechanism, and
it was the wrong one.

## 46.3 `ETry` deleted the expression it protected

```fstar
| ERaise _ | ETry _ ->
  K.EAbortS "Custard: exceptions are not supported by the C backend"
```

For `ERaise` an abort is defensible. For `ETry` it is not conservative --
it **discards the protected expression**. A `try safe 7ul with _ -> 99ul`
whose body never raises became

```c
uint32_t TryOk_attempt(void)
{
  KRML_HOST_EPRINTF(...);
  KRML_HOST_EXIT(255U);
}
```

The call to `safe` is gone. Not the wrong answer -- no answer. And karamel
reported only `Warning 242: the exception TryOk.Boom has no karamel
counterpart and was dropped`, and exited 0.

`ETry` is now refused, as the direct C backend has always refused it
(`PrintC.fst:1036`). `ERaise` may stay an abort **because** `ETry` is
refused: with no handler anywhere in an accepted program every raise is
uncaught, and abnormal termination is what an uncaught raise means. That is
also what keeps `krml_typ`'s `TExn -> TAny` honest, since the value is never
inspected.

One thing round 46 raised about §44.1's own fix. `krml_reject`'s shared
second line said the direct C backend *may* accept the construct, and the
hedge was wrong at four of its six sites: a string and a float pattern
survive the crossing; a pattern disjunction, a pattern guard, a constant
pattern of no known kind and an exception handler do not. Sending a reader
to a backend that will refuse them too is worse than saying there is nowhere
to go. The sentence is now per-site, `krml_reject_c_ok` against
`krml_reject`, and `TryOk` pins the absence of the wrong one.

## 46.4 What a `NOEGREP` does not check

Round 44 added `NOEGREP_PatStrKrml += "not supported by the C backend"`,
which pins the phrase as absent from *that test's* output. It was absent,
and the test passed, and the phrase was still emitted by two other sites in
the same file -- one of which put it in a Rust binary.

The check worth having was never about one test's output. It was whether
the compiler can still emit the sentence, from any site, reached by any
program, and

```
grep -n "supported by the C backend" src/custard/*.fst
```

answers that in a second. It is now `make check-sources`, and it runs as
part of `all`.

This generalizes past the one phrase. A test pins what a program produced;
some properties are about what the compiler *contains*, and those want a
check over the sources, not over an output. The two are not substitutes,
and the cheap one had been left out.


# 47 What C and C++ disagree about

Round 47 came from a reviewer who compiled the generated code with a
*different compiler for the same text*, and found a construct on which the
two disagree silently. It also closed §45.4's open question, in the
direction nobody had proposed.

## 47.1 A nested enum is invisible from C++

Every tagged union Custard emitted looked like this:

```c
struct CExtern_cmd_s {
  enum {
    CEXTERN_NOP,
    CEXTERN_SKIP,
    CEXTERN_BUMP
  } tag;
  union { ... } val;
};
```

In C, the enumerators of an enum declared inside a struct have **file**
scope: they leak out of the struct, and `CEXTERN_BUMP` at a use site
resolves. In C++, an unnamed enum nested in a class has **class** scope: the
name is `CExtern_cmd::CEXTERN_BUMP`, and the bare form does not exist.

```cpp
struct S { enum { A, B } tag; };
int main() { S s; s.tag = A; }   /* C: fine.  C++: 'A' was not declared */
```

So every discriminated union Custard produced was unusable from C++ or from
CUDA, which is C++. Seven of the suite's units failed under `nvcc`, all with
the same message, while all 34 compiled clean as C11 under `gcc` *and* under
`clang -Weverything`, which reported nothing -- correctly, because as C the
code is right.

The fix is to declare the enum beside the struct rather than inside it,
which is still valid C11 and changes neither the meaning nor the layout:

```c
enum CExtern_cmd_tags { CEXTERN_NOP, CEXTERN_SKIP, CEXTERN_BUMP };
struct CExtern_cmd_s {
  enum CExtern_cmd_tags tag;
  union { ... } val;
};
```

`enum_tag` derives from `c_name` exactly as `struct_tag` does, so §32.9's
header renaming follows without further work.

The `extern "C"` wrapper the header already carried does not help, and it is
worth being clear why: **linkage is not scope.** `extern "C"` changes how a
name is mangled for the linker. It does not change where C++ looks the name
up, and this bug is entirely about lookup.

### The test leg this needed

`tests/custard` now compiles every generated unit a second time, as C++17,
with `-fsyntax-only`. Custard does not target C++ -- the object file is
still the C compiler's job -- but a generated header is *meant to be
included by a consumer*, and CUDA is the consumer Kuiper has. The second
front end is the whole point: it is the only thing in the suite that could
have seen this, because everything the C leg checks was already right.

All 34 units pass it, with `-Wall -Werror`, which is the other half of the
finding: this was one construct, not a class of them.

The negative control is the cleanest one this document has. Put the nested
enum back by hand and the same file compiles with `gcc -std=c11 -Wall
-Werror` at rc=0 and fails with `g++ -std=c++17` on the first use of a tag.
Two compilers, one text, opposite answers, no diagnostic on the side that
was being tested.

## 47.2 An external type may be indexed after all

§45.4 recorded an open question: whether a rule could *generate*
per-configuration C names from erased F\* indices, using §34.1's reduced
rule arguments. The answer is that no rule is needed, because F\* already
has the mechanism -- a typeclass whose indices are erased, resolved by
instance selection, which Custard monomorphizes correctly today.

```fstar
class frag_cfg (knd : kind) (m n k : en) = {
  alloc : unit -> ML (frag knd m n k)
}
instance cfg_a : frag_cfg FragA e16 e16 e16 = { alloc = mk_a }
```

A body polymorphic in the configuration extracts to the same C as a
hand-written one; the dispatch disappears and the instances pick the target
names. `tests/custard/FragCfg.fst` is that shape at C11 scale, and checks
its own answer.

What did *not* work was writing the external type with its indices:

```fstar
[@@custard_extern "fc_frag_t"; custard_c_header "FragCfg_stubs.h"]
assume val frag (knd : kind) (m n k : en) : Type0
```

which gave `Error 368: the polymorphic type FragCfg.frag has no C
representation`. `decl_of` resolves an external only at `TApp (n, [])`, and
§30.11 rule 4 froze the type -- a type in an external's signature must not
be cloned, because a clone would name a declaration the realization does not
define.

That reasoning is right in general and **vacuous when the frozen type
carries its own C name.** An external type's spelling is a fixed string
taken verbatim (§45.1), with nowhere in it for an argument to go -- indexed
`TExtern` was proposed and withdrawn in round 45 -- so `frag FragA 16 16 16`
and `frag FragAcc 16 16 16` are both `fc_frag_t`, and there is nothing for a
realization to fail to define.

So `mono_cty` now drops an external type's arguments outright. No clone is
requested, so there is nothing to freeze; the declaration is kept (with its
parameters dropped) because it is what carries the `Extern` flag that
`decl_of` reads. The workaround -- an unindexed external plus an abbreviation
carrying the indices -- still works and is arguably better style, but it is
no longer forced.

### Two things the configuration idiom requires

Both are consequences of existing rules rather than new ones, and both are
easy to get wrong:

- **Erase every index the C side does not take.** An index left concrete is
  passed to the external as an ordinary argument. As a `nat` that is `Error
  368: the unbounded integer literal 16 has no C representation`, which is
  correct but indirect -- the index was only ever there to select an
  instance. As an *enum* it is worse: the call goes out as
  `wmma::mma_sync(CFG_RM, CFG_RM, c, a, b, c)`, silently wrong, because
  nothing can tell Custard that an external's leading arguments are
  spurious.
- **`inline_for_extraction noextract` belongs on the class, not only on the
  instances.** On the instances alone the projectors survive as real
  wrappers -- and under CUDA a `static` wrapper is `__host__`, so `nvcc`
  rejects a `__global__` caller.

## 47.3 The krml path cannot carry a C++ name

For completeness, since §45.3 made the same program *nearly* work through
karamel. It does not, and will not without changes to karamel:

- karamel sanitizes names of its own, downstream of Custard, so
  `wmma::fill_fragment` becomes `wmma__fill_fragment` and `auto&` becomes
  `auto_` -- the §45.1 bug again, in the other repository.
- karamel emits a prototype for an external that already has a declaring
  header. `PrintC` suppresses that (`extern_decl` returns `None` when a
  header is present, §45.1); karamel has no such rule, so a function-like
  macro target collides with its own prototype.

None of this is a Custard bug and none of it blocks the consumer, since C is
the destination. It is recorded so that **a C++-qualified target is a
direct-C-backend feature**, and nobody spends an afternoon on the krml
route.


# 48 Where the two backends disagreed about strings

Round 48 found no bug. It reported one refusal that cannot be reached, one
gate four characters too narrow, and -- as an offer rather than a defect --
that the krml backend's refusal of string patterns was never forced. This
section records all three, plus a cross-reference slip of our own and three
things that turned out to be already right.

## 48.1 A refusal that could not be reached

`krml_pat`'s fallback for an unclassified constant pattern

```fstar
| _ -> krml_reject_c_ok "this constant pattern"
```

became unreachable at §46.1, when `FStar.Char.char` was added to `prim_type`
and `CChar` joined `CUnit`, `CBool` and the two `CInt`s above it. All six
constructors of `const` are now covered by a named case.

Dead code is not itself worth a section. What is worth one is *which*
refusal it was. `krml_reject_c_ok` appends a sentence telling the reader
that the direct C backend does accept the construct, and that is true of
exactly two of the six things `krml_reject*` is called for -- string and
float patterns. It was false for a disjunction, a guard and a handler, which
is what §46.4 split the function to fix. The fallback kept the generous
message, so it was *also* wrong, silently, and would have started lying on
the day a seventh constant constructor was added -- which is precisely the
day someone reads it.

The fix is to say what is true of each:

- `PConst (CString _)` -> `krml_reject_c_ok`, and after §48.3 it is only
  reachable for a *nested* string pattern, which `PrintC` still accepts.
- `PConst (CFloat _)` -> `krml_reject_c_ok`, with a comment recording that
  it is unreachable from source: **F\* rejects a float literal in pattern
  position at parse time**, Error 168, *"This is not a valid numeric
  literal"*, for both `1.0` and `1.0f`. Kept because the IR can hold one
  even though the parser will not build one.
- `PConst _` -> the strict `krml_reject`. If a seventh constructor appears,
  the default claim is the safe one.

The general rule: **a fallback should carry the weakest claim, not the
claim that happened to be true of the cases it was written for.**

## 48.2 An interface file is a source file

`make check-sources` (§46.4) greps the Custard sources for a diagnostic
phrase that no longer has a right to exist. Its target was

```make
CUSTARD_SRC := $(wildcard $(CUSTARD_DIR)/*.fst)
```

which is 18 files, and misses the 18 `.fsti` beside them. No interface
currently carries any diagnostic text, so the gap was latent rather than
live -- but a check whose reach is smaller than its subject is a check that
will pass for the wrong reason exactly once.

`$(wildcard $(CUSTARD_DIR)/*.fsti)` closes it. The negative control put the
phrase into an `.fsti` and confirmed the check fires.

## 48.3 A string match becomes an if-chain

§44.1 refused a string pattern on the krml backend, because karamel's
`pattern` has no constructor for a string constant and the one Custard was
substituting matched everything. The refusal is correct as a statement about
karamel's AST. It is not, however, forced -- and the observation that makes
it unforced is that **karamel handles string *equality* perfectly well**:

```c
bool __eq__Prims_string(Prims_string s1, Prims_string s2)
{ return (strcmp(s1, s2) == 0); }
```

which is `krmllib/c/prims.c:24`, and is exactly the comparison `pat_tests`
already builds by hand for the direct C backend (§44.2).

So the pattern is redundant. `PrintKrml` now desugars a string match into
the same if-chain:

```c
uint32_t classify(Prims_string s)
{
  Prims_string scrut = s;
  if (__eq__Prims_string(scrut, "a")) return 1U;
  else if (__eq__Prims_string(scrut, "b")) return 2U;
  else return 3U;
}
```

Three things about the shape:

- **The scrutinee is bound once.** It may be a call, and the chain mentions
  it once per branch.
- **The guard fires only on a flat match** (`is_string_match`): the
  scrutinee's type is a string and every pattern is a bare string constant,
  a variable or a wildcard. Anything else -- a string inside a constructor
  pattern, a `when` clause -- falls through to the general path and is still
  refused. `PatStrNest` is the negative control.
- **A catch-all is required.** F\*'s exhaustiveness check supplies one for a
  string match, so the requirement costs nothing; without one there would be
  no expression to end the chain with, and inventing an abort there would be
  a translation rather than a refusal, which is what §46.3 was about.

### The encoding that made it fail first

The first version emitted the equality as a bare `K.EApp (K.EOp (K.Eq,
K.Bool), args)` and karamel dropped both definitions with

```
Malformed input: subtype mismatch: Prims_string vs: bool
```

then generated calls to functions it had not declared. **Decidable equality
is polymorphic in karamel and is typed only through an explicit type
application** -- `ETypApp (EOp (Eq, _), [t])`, `Checker.ml:592`. Left bare,
the checker reads the operator's *width* as the operand type, concludes the
arguments should be booleans, and rejects.

Custard already knew this: the null-pointer comparison a few lines above in
`krml_expr` carries a comment saying so, and the general `EOp` case handles
`Eq`/`Neq` at `po_ty = None` the same way. The new code simply had to do
what the code beside it was already doing. Worth recording because the
failure mode is quiet in the usual invocation: with `-silent`, karamel drops
the definition without a word and the first symptom is a C compiler
complaining about an implicit declaration.

### What the test needs, and what it does not

`PatStrKrml` was a reject test for two rounds and now runs. It gets its
strings from a malloc-ing external for the same reason `PatStr` does: a
program whose strings are all literals exits 0 either way, because the C
compiler pools literals and the addresses then agree by accident (§44.2).

It also supplies `__eq__Prims_string` from its own stub header. That is not
a Custard dependency: the suite links against krmllib's *minimal*
distribution, which does not carry `prims.c`, and any F\* program that
compares two strings through the krml backend needs the symbol whether or
not it ever writes a pattern. A real build links `prims.c`.

## 48.4 A cross-reference that pointed at the wrong section

Round 47's commit put `Section 48.1` and `Section 48.2` into six source
comments and three test files. Those numbers are the *reviewer's*; this
document's are one lower, and have been since §46. The comments therefore
pointed a reader at a section that did not exist yet.

Corrected, and recorded because the cause will recur: **the reviewers number
their rounds independently of this document's sections**, and a round
report's own headings must be renumbered on the way in, not copied. The
divergence was already stated in a PR reply; it needed to be stated in the
sources too, where a reader of a comment actually is.

## 48.5 Three things that were already right

Round 48 spent most of its effort on negative results, which are recorded
here so they are not re-derived.

**`builtin_type` and `prim_type` agree, with one deliberate exception.**
They are a pair of tables that have to be kept in step and nothing enforces
it -- which is what §46.1 was, in both directions at once. After that fix
`builtin_type` is a subset of `prim_type`, and the single remaining
divergence is correct: **`Prims.int` is in `prim_type` and deliberately
absent from `builtin_type`**. Unbounded arithmetic has no C11 representation
and the direct backend refuses it with a real message; the krml path maps it
to `K.CInt` and lets karamel reach for `krml_checked_int_t`. A genuine
difference in what the two backends can do, not a gap.

**`krml_op` is total.** Twenty-two operators, no catch-all, one-to-one. The
`| _ -> K.CInt` width fallback at the `EOp` site is reached only when
`po_ty = None` and the operator is arithmetic, which is exactly `Prims.int`,
which is exactly `CInt`.

**Round 44's fix has no surviving sibling in C.** Every site in `PrintC`
that can emit `==` was audited: two are enum tags, two are `NULL`, and two
are the string pair itself. `infix_op` has exactly one caller and the string
case sits before it.

To which round 48 added one of its own, and it is the one worth keeping:
string `==` was fixed in the direct C backend in round 44 and *the krml
backend was never asked the same question*. It happened to be right --
`EOp Eq` at string type goes through the polymorphic path to
`__eq__Prims_string`. But "fixed in one backend, never checked in the other"
is the shape of §46.1 and of §44 and of this section's own §48.3, and the
cheapest place to catch it is at the moment of the first fix.


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
| M8a | Type monomorphization: one declaration per instantiation (§5.0.1), which unlocks per-instantiation layouts | Done.  The pass and `MonoTypes` were built with M8c; what closed the milestone was the exit criterion, re-running the *whole* corpus under `--custard_monomorphize_types`, which seven of thirty-three modules failed.  One cause, in two halves: a `Realized` type was cloned, and the clone named a member of a hand-written OCaml module that does not define it (`FStar_Pervasives_Native.option__int`).  Freezing those declarations, as §5.0.1 rule 4 already froze the types an external's signature mentions, fixes six; the seventh needed the distinction between *naming* a declaration and *cloning* it (`Monomorphize.shape_of`), since a frozen type's fields are still at the arguments the use site wrote and dropping them left a `[]` pattern unrenamed under a cloned `list`.  Only on the OCaml path: in C nothing is realized by hand and freezing would leave a type variable, which C cannot size |
| M8b | Direct-to-C backend (§6): self-contained C11, no krmllib, function pointers but no closures | Done.  `PrintC`, and the rejections by name of what C cannot express (error 368) — closures, exceptions, unbounded `Prims.int`, pattern disjunctions and guards, and a datatype containing itself by value — which `CNoInt` and `CNoClosure` pin.  The exit criterion that was still open is that the two Pulse modules were *compiled* and not run, because their `main` returned a computed value and so a nonzero exit status; each now checks its own answers and returns 0, and the suite runs the binary.  That is what makes the array, the struct-valued cell and the function pointer of `PulseHashTable` tested rather than merely accepted by a C compiler.  Still open, and noted in §12.8 item 8: `PrintKrml` maps `Prims.int` to a fixed-width integer, which the direct backend rejects outright but the krml path does not |
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
| M10p | **Plugin registration** (§13) | Done.  `FStarC.Custard.RegEmb` generates the registration for a `[@@plugin]` in a module named by `--custard_entry`, and the `e_<name>` for a `[@@plugin]` datatype with it, as F\* syntax handed to `Extract.expr_of_term` rather than as IR (§13.1, §13.4).  All 25 ulib plugin modules are roots in `entrypoints.txt`, and the acceptance test --- a source file declaring a typeclass, checked by the Custard-built `fstar.exe` --- passes.  The recursion in a generated embedding is tied by *substituting* the sub-embedding into the closure that uses it, not by binding it: a `let` hoists the knot out of the closure and the group diverges during module initialization (§13.4).  Fallout in the shared machinery: `Parser.Dep.deps_of` now parses a file the dependency scan never reached (§13.3), and `Extract` normalizes a definition body, its result type and its reification under the binders the specialization kept --- `FStar.Tactics.Util.map : ('a -> Tac 'b) -> ...` reifies to a comp whose universe mentions `'b`, and the top-level environment does not bind it.  Four miscompilations that only a running compiler could expose are in §13.5, the first of them the rule that a reduction whose reduct will be compiled must not fold a primitive step with an unrepresentable result (`Env.SafePrimops`, error 370) |
| M10o | **The `FStar.Stubs.*` rename** (§8.2) | Done.  `Builtins.no_fstar_stubs`, applied in `Extract.name_of_lid`, so that a plugin's `FStar.Stubs.Tactics.Types.proofstate` and the compiler's `FStarC.Tactics.Types.proofstate` are one name.  Fallout: `solve` is now `inline_for_extraction` in its five copies (its `{| ev : a |}` binder made `#a` `Mono`, which §3.2b rejects once `embedding` is no longer specialized), and record ascription had to cover projections as well as record expressions (§5.5). |
| M10d | A Custard-compiled plugin linking against a Custard-compiled compiler (§12.8 item 4) | Done, and it is `make custard-plugin` (§12.12).  A `.cui` entry now records the *file* a declaration was emitted into (`ue_home`), not just the unit, because the compiler is built split; an import that carries one is folded into the printer's `homes` table, since an import from a split producer and a cross-file reference inside a split output are the same thing.  `Loader.ensure_loaded` registers a module's dependences before the module, which a plugin run needs and a whole-program run got for free.  The test reduces `irreducible` definitions with `norm [primops]`, so it fails without the plugin.  It exposed the sixth miscompilation of §13.5: specialization eta-expanded `Cfg.cached_steps`, reallocating its memo table per call, and the extracted compiler folded no primops at all |
| M10q | Cleanup: bounded normalization everywhere, target-native tuples and `option` | Done.  Every normalization Custard performs now runs under `--custard_norm_budget`, through `Extract.norm_bounded` or the new `Mono.norm_bounded` for the callers below the extractor; the four sites in `Mono` and `RegEmb` that did not were the last unbounded ones (§12.8 item 8).  And a realized type that the realization defines as an *alias* of a type the target already has is printed as that target type: `FStar.Pervasives.Native`'s `tupleN` in OCaml's tuple syntax and its `option` as OCaml's `option`, so that no Custard-generated line in the extracted compiler names `FStar_Pervasives_Native` (§8.2).  `fst`/`snd` are `inline_for_extraction` |
| M10r | Extract the Pulse checker (§12.13) | Measured, not finished.  `Pulse.Main` extracts whole against the compiler's `.cui`, with no `--warn_error` suppression --- 7.6k lines, and both registrations come out correct: `check_pulse`'s nine-argument one and, since M10s, `check_pulse_after_desugar`'s polymorphic one.  Pulse needs no new `Builtins` entry and no output splitting, since its realizations name no Pulse module.  Every compiler symbol its realizations name now resolves against `stagec/build`, and `Pulse_RuntimeUtils.ml` compiles there.  Superseded by M10v, which compiles it |
| M10t | **Plugin-supplied entry points** (§12.11, §12.13) | Done.  `--custard_entrypoints FILE` reads a file of roots --- one per line, `#` for comments --- so the format is the compiler's rather than a `sed` in the makefile, and so a *plugin* can ship one: the compiler is built before the plugin exists, and a realization's callees have to be in the binary the plugin is loaded into.  `mk/custard.mk` now passes `src/custard/entrypoints.txt` and `pulse/src/custard-entrypoints.txt` this way, and takes more in `CUSTARD_ENTRYFILES`; `make custard` is itself the test, since all 328 compiler roots now arrive through the new option.  Six of the seven compiler symbols `Pulse_RuntimeUtils.ml` needs now resolve against `stagec/build` |
| M10u | **A realization calling a monomorphized compiler function** (§12.13) | Done.  The seventh symbol, `FStarC.FlatSet.union`, could not be an entry point: its typeclass dictionary is a `Mono` binder and a root has no call site to specialize it at.  A `Mono` binder wants a call site, so `PulseSyntaxExtension.Env` --- a Pulse F\* module already built `--with_fstarc` and already named by the realization --- now gives it one, in two three-line wrappers at the types Pulse actually uses.  The instance has to be brought into scope with `open FStarC.Syntax.Free {}` rather than passed with `#`, since a `{| |}` binder is not an implicit one (error 189).  They specialize to `FStarC_Syntax_Unionfind.fStarC_Class_Setlike_union__ctx_uvar`, which the compiler already has, so no entry point was needed after all.  `PulseSyntaxExtension_Env.ml` and `Pulse_RuntimeUtils.ml` now both compile against `stagec/build` with nothing unresolved |
| M10s | **Polymorphic plugins** (§13.4) | Done.  A `[@@plugin]` with leading type binders registers: the type variable's embedding is `mk_any_emb` on the type argument, and a generated match peels one argument per type binder off the front of the primitive step's argument list, so the registered arity counts the type arguments while the combinator's index does not.  Only leading type binders; one after a value binder is still rejected.  `tests/custard/plugin` adds `pid`, `psnd`, `pcount` and `pswap` (the last putting an identity embedding *under* an `e_tuple2`), all `irreducible`, so the test fails with error 228 without the plugin loaded.  Specializing `mk_any_emb` into a plugin also exposed that `Extract.import` never filed a linked declaration in `st.emitted`, so every cross-unit call was typed `TAny` and classified `E_Pure` --- `!Options.debug_embedding` printed as an array index, and an imported effectful call could have been dropped |
| M10v | **Compile the Pulse plugin** (§12.13) | Done.  `checker` and `syntax_extension` extract as two units, the second linked against the first --- 33 generated files become 13 --- and compile together with the four realizations and the two menhir grammars into one loadable `.cmxs`.  Rules the exercise settled: a unit does not export its `DExternal`s, because they are the holes it leaves and one of them (`parse_pulse`) is another unit's definition (§12.2); a cross-unit callee needs an entry point, since a call across a unit boundary is not a request Custard can see; and two units cannot share one checked-file cache, because `Pulse.Main.fsti` and `PulseSyntaxExtension.ASTBuilder.fsti` exist in both trees with different contents.  Left: the `extraction` unit, a Custard-flavoured `Pulse_Extract_CompilerLib.ml`, and folding the recipe into `pulse/mk` |
| M10w | **Ten extraction bugs the Pulse plugin exposed** | Done, each with the rule it violated: a `reify` stuck in front of a local `let rec` (§7.5); a realized type's record-versus-variant shape, arity and projectability, all of which the realization owns and not Custard (§8.2, new `SourceRecord` flag); a result type peeled at the `cty` level, where an abbreviation is a name and not an arrow, so an eta-short definition claimed an arity it did not have (§7.3, `tests/custard/RetArity.fst`); a lambda that loses all its binders, where `expr_of_term` had a purity test `Mono.keep_thunk` says it must not have; four coercion boundaries the pass could not see --- an imported *value* signature, a structured pattern under an `any` field, a comparison, an application head (§5.4); and a `GTot` result judged on its uninstantiated type variable, which left a call to `Pulse.RuntimeUtils.magic` in the output (§5.1).  `tests/custard/Realized.fst` and `RetArity.fst`; the compiler's own build covers the realized-*record* case, `FStarC.Parser.ParseIt.code_fragment` |
| M10x | **Run the Pulse plugin** (§12.13) | Done.  The `extraction` unit makes it three, and the three link into one `.cmxs` that loads into a Custard-built compiler and checks all 58 files of `pulse/test`.  Three bugs stood in the way, none of them about separate compilation: a `[@@plugin]` module that was not a root, so its tactic got stuck with no diagnostic (§13.3, `tests/custard/plugin/CustardPluginAux.fst`); a duplicated `Stop` exception, which OCaml gives an identity per declaration, so the plugin raised what the compiler could not catch (§8.5, new `Builtins.stub_aliases`); and a recursive call assumed pure, so §7.3 deleted the first of `walk l; walk r` and Pulse's dependency scanner stopped traversing half of every statement --- a silent miscompilation that had been there from the start (§7.3, `tests/custard/RecEffect.fst`) |
| M10y | **`make custard-pulse-plugin`** (§12.13) | Done.  The three extractions, the link and a load-and-check smoke test are `mk/custard.mk`'s `pulse-plugin` target, so the Pulse plugin is a regression rather than a demonstration.  `pulse/src/ml/custard/` holds the one realization whose field names differ from ML extraction's, replacing the `sed` the script used.  Two checked-file rules the exercise settled, neither about Custard: the prelude has to come from `stage2/ulib.checked` and not from the installed `fstarc/src.checked`, whose flavour of `Prims` carries a different bundle hash; and `--already_cached` keeps only its last setting, so the `DEPFLAGS` one that `pulse/mk` suggests is dead |
| M10e | Structural specialization suffixes over all `Mono` arguments (§12.3) | Done. `Extract.hint_of_term`/`hints_of`/`fit`, and lifted locals inherit their enclosing suffix. 243→121 numeric, 409→204 fallbacks, 225→100 chars |
| M10z | **Output layout** (§6) | Done.  `Simplify.float_lets` turns the nest of definiens-position bindings ANF leaves behind into a flat chain, and the OCaml backend prints a run of bindings and statements at one column inside one pair of parentheses, a discarded expression with `;` (through `ignore` when its type is not unit), and a record --- declaration or literal --- one field per line unless it fits in 80 columns |
| M10α | **Higher-kinded `Mono` arguments** (§5.9) | Done.  A higher-kinded argument arrives as a lambda, so substituting it leaves a beta-redex in type position, whose head is a `Tm_abs` and which nothing normalizes: `ty_of_typ` read it as `any` and a state monad written against `FStarC.Class.Monad` came out as `Obj.t` with an `Obj.magic` at every bind.  Reducing it takes the compiler's own output from 528 `Obj.magic` to 80 and from 21 `Obj.t` to 11, `FStarC.SMTEncoding.Pruning` included.  `tests/custard/MonoState.fst` |
| M10β | **Performance of the extraction** (§12.14) | Done.  `--profile_component FStarC.Custard` now prints an *exclusive*-time breakdown, from Custard's own `Prof` rather than `FStarC.Profiling`, because a mutually recursive traversal's inclusive counters all report the outermost frame.  It found three accidentally quadratic spots: `Loader.loaded` scanned every loaded module on every name resolution (27 s of 77), the `Mono` binder-flag queries were recomputed at every call site rather than per declaration (4 s), and `unit_entries` looked each declaration up by linear scan (6.9 s to 65 ms).  Extraction of the whole compiler goes from 77 s to 50 s and `make custard` from 3 min 45 s to 3 min 3 s.  What remains is flat; the build stages, MENHIR's 51 s and `ocamlopt`'s 78 s, are both sequential work on a 256-core machine and are the larger target |
| M10γ | **A dune build for Custard** (§12.11) | Done.  `mk/custard.mk`'s hand-rolled menhir and `ocamlopt` stages are replaced by a dune project generated into `stagec/dune/`: a `wrapped false` library over `stagec/split/`, `src/ml/` and `ulib/ml/plugin/`, plus a one-module executable.  Dune's `menhir` stanza does the `--infer` pre-pass against *this* library, which was the reason the build was hand-rolled in the first place, and does it without the best-effort `ocamlc -c` of every module.  `-linkall` moves onto the library, so that `fstar.lib`'s `FStar_Order` is not force-linked against Custard's own.  129 s of build becomes 18 s, and `make custard` 3 min 3 s becomes 1 min 19 s.  Plugins now link against `.fstarcompiler.objs/{byte,native}` |
| M10δ | **Master merge: the simplified effect system** | Done.  `comp_typ` lost `effect_args` and gained `comp_pre`/`comp_post`, so `Extract.key_of_comp` hashes those instead, and `TypeChecker.Env.lift_comp_t` and `polymonadic_bind_t` left `src/custard/entrypoints.txt` with them.  It also uncovered two extraction bugs that had been latent: `callee_eff` read an *over*-applied callee's effect off the declaration rather than off the surplus arrows of its result type, which is exactly the shape §7.5 gives every reified `Tac` call, so `tcresolve' st0; ...` was deleted as pure and no typeclass constraint in ulib could be solved by the extracted compiler; and the coercion pass asked nothing of an argument whose position an untrusted head still typed concretely, so a dependent pair's realized `any` second component reached a `comp` parameter (§5.4) |
| M10ε | **The DICE example, through both C backends** (§14) | Done.  `pulse/share/pulse/examples/dice` extracts from its six entry points to 1535 lines of C through karamel or 968 lines of C directly, each compiling with `-Wall -Wextra -Werror`, and the direct output includes four C standard headers and six lines of the example's own and nothing else -- no krmllib, which is the point of replacing karamel rather than sitting on top of it.  `custard.Makefile` builds either.  Eleven compiler fixes and *no change to the example's F\* sources*, all of them general: abbreviations unfolded in binder queries (§14.1), `extract_as` on a `val` (§14.2), `n_extra` counting erased binders (§14.3), eta expansion bounded by the callee's arity (§14.4), external types, by attribute or by `--custard_extern_type` (§14.5), globals with computed initializers (§14.6), let-bound lambdas inlined at their call on the C backend only (§14.7), abbreviations canonicalized before a type instance is keyed (§14.8), a match whose last test pruning deleted (§14.9), `void` where C means it (§14.10), and empty blocks (§14.11).  Three of the eleven were caught by a regression rather than by the example: `tests/custard/EraseAbbrev`, `make custard-smoke`, and the empty-block invariant §14.11 added, which immediately caught an empty `custard_init_globals` left by §14.6.  `tests/custard/CExtern` is the new C test, covering both spellings of an external type, a computed global, and a unit-valued match with do-nothing arms |
| M10ζ | **The Pulse test suite** (§15) | Done.  All twenty extraction tests in `pulse/test` go through Custard, ten of them straight to C, four through karamel because they compute on `Prims.int` (§15.2), six to OCaml, and the `.expected` files were regenerated.  The enabling piece is `--custard_entry_module`, which roots every top-level value of a module (§15.1) --- a test module has no `main`, and listing its `fn`s in the makefile would let a new one silently stop being extracted.  Rooting a *module* means rooting its specifications too, so a root now skips an erased definition.  Five fixes, three of them about the karamel path the DICE example barely used: karamel prepends its own `Prims` and rejects ours as duplicates, `-bundle X=*` needs `X` to exist, and a `BufIsNull` without a type application was silently *dropped* by karamel’s Low\* re-check, taking `Null_test` with it.  The other two: an `if` whose arms are both empty, caught by §14.11’s invariant, and a `null` an OCaml `ref` can actually hold --- the immediate `0`, tested with `Obj.is_block`, since a sentinel allocation is not one value under `--custard_split`.  `pulse/mk/custard-test.mk` |
| M10η | **The cross-backend matrix** (§16) | Done.  All four Custard columns of `tests/extraction/backends` -- OCaml, direct C, and karamel's C and Rust off one shared `.krml` -- run green over the suite's twenty-five modules, each extracted, compiled and *run*, with its exit status compared against what F\* proved.  Four bugs in Custard: the OCaml entry point discarded the exit status §4.4 promised; C integer literals carried no width suffix, so `((uint64_t)18446744073709551615)` did not compile (a decimal literal takes the first *signed* type it fits, C99 6.4.4.1, and the cast cannot rescue it); `Int8`/`Int16` modular operators were not truncated back after C's integer promotion, so `~(uint8_t)0` was `-1`; and, severity 2 on every backend, `Layout.rw_expr` fused nested casts unconditionally, so `uint8_to_uint32 (uint32_to_uint8 x)` became bare `x` -- sound for a representation coercion, a silent miscompilation for a width conversion.  One bug left open and written up as finding #18: only `FStar.UInt8` is a realized module, so `ne`, `lognot`, `shift_arithmetic_right`, the rotates and the masks at the other seven widths are compiled from their bit-vector *model* in `Prims.int`.  A `custard_xfail_rule` was needed because Custard is the extractor, so a bug in it can fail the F\* step, which the existing rule takes as a prerequisite.  Custard passes five cells the older pipeline XFAILs (§16.5) |
| M10θ | **Two things about the C output** (§17) | Done.  A global whose initializer is a C constant expression is now emitted as `int32_t m7 = ((int32_t)-7);` rather than assigned at startup, so the linker can put it in `.data`/`.rodata` and the C compiler can fold it at its uses; `ExtIntSigned` loses its `custard_init_globals` and its call from `main` entirely, and `CExtern` pins a module that keeps the function for the two globals that still need it.  The recognized subset is a constant and a cast of one: wider arithmetic is pointless (`2 + 2` has been folded long before `PrintC` sees it) and a record is not merely pointless but wrong, since the compound literal Custard emits for one is not a constant expression at file scope.  And the IR's single cast node is split in two: `ECoerce` for §5.4's representation coercion, which computes nothing and therefore fuses, and `ECast` for §8.1's machine-integer conversion, which computes and therefore does not.  They were one node, and §16.2's severity-2 miscompilation was §5.4's fusion rule applied to a conversion; the fix then was a side condition testing whether both sides were `TInt`, which works but asks every pass to re-derive a fact the front end knew.  The split removes the side condition from `Layout`, removes a clause from `Driver.lost_cast`, and turned up the same latent bug a second time in `PrintOCaml.index`, which looked through a narrowing conversion to keep a subscript readable |
| M10ι | **Recursive datatypes in the direct-to-C backend** (§17.3) | Done.  A struct reaching itself through a pointer is legal C and `check_finite` correctly accepts it, but `PrintC` emitted every struct as an anonymous typedef, so a field naming the type under definition named something that did not exist yet -- and no ordering of the declarations can fix that, since that is what recursion means.  Every struct now carries a tag `t_s` and every tag is forward-declared in one block ahead of all the definitions, which makes the order irrelevant rather than merely computable.  Reported against EverParse's `cbor_raw`, where it was the *only* defect: with tags added by hand and nothing else changed, the output compiles clean under `-std=c11 -Wall -Wextra -Werror`.  `tests/custard/CRecType.fst` pins the three shapes that failed differently, compiled and run |
| M10κ | **Erased arguments in a call through a variable** (§18.1) | Done.  `arrow_formals_comp` stops at an abbreviation, so a definition whose codomain is one looks shorter than it is and every argument past that point goes unfiltered -- which passes at runtime the erased arguments the callee deleted, as a `()` in a position that no longer exists, shifting the rest of the spine.  `classify`, `unit_binders` and `type_binders` have unfolded since EverCrypt's `compute`; `erased_binders`, which filters the spine of a call through a *variable*, had not.  Split into `erased_binders_unfold` rather than changed, because filtering a definition's own binders wants flags aligned against `arrow_formals_comp` and filtering a call spine wants flags as long as the call.  Reported against EverParse's CBOR stack as `unbound variable pm reached the karamel backend`: a Pulse `fn rec` hands its recursive call to its body as a closure, so the head is a local whose sort is an abbreviation.  `tests/custard/EraseAbbrev` gains the variable-headed half of a case it already had by name |
| M10λ | **An arity indexed only by values is a type parameter** (§18.2) | Done.  `is_type_param` held of kind `Type` and nothing else, on the ground that no target has a type variable standing for a type constructor.  True of `m:Type -> Type`; false of `b:header -> Type`, which takes a *value*, and values are erased from the target's type language, so it denotes exactly one target type.  Dropping it left `dtuple2`'s second field typed by a name no parameter bound -- `any`, which direct-to-C rejects outright and which the krml path turns into a `(void *)` cast gcc rejects.  Three pieces: `is_value_indexed_arity`, translating an application `b x` as the parameter itself, and translating the argument lambda `fun h -> payload h` as its body.  It also un-breaks `FStar.Set.set`, whose abbreviation no longer needs `has_unrepresentable_param` to unfold it and so reaches §13.5's result-type peel as a `TApp`; the peel goes through `head_ty` now.  Reported against EverParse as the highest-impact item: this is the whole LowParse idiom, a parsed header indexing the payload's type, and it was `any` throughout |
| M10μ | **The request chain reaches the normalization budget below the extractor** (§18.3) | Done.  Error 365 is only useful if it names the definition being reduced.  `Extract.norm_bounded_in` always did, from the request chain of §3.6; `Mono.norm_bounded` did not, and it is the one that fires on type-level work -- a binder's sort, a binder's kind, an arrow spine -- which is exactly the case the EverParse report had to bisect a module to explain.  `Mono.chain_reporter` is a `ref` to a reporting function that `Driver` points at `Extract.request_chain`, defaulting to reporting nothing so that `Mono` stays usable with no extraction in progress; a hook rather than threading the extractor's state through every arity test.  `is_value_indexed_arity` also became syntactic-first in the same pass, looking for the arrow before it normalizes anything, since `is_type_param` is asked about every binder of every definition and the overwhelming majority are values that stop at `Cons?` having paid nothing.  Reported alongside a 6m30s whole-module extraction that no local sweep reproduces as super-linear; keys are per-call-site, so more roots mean more output, and whole-program remains the intended workflow with many `--custard_entry` runs a bisection tool rather than a speed-up (§18.3). |
| M10ν | **Retest fixes: by-value type order, fv-headed spines, unbound names in C** (§19) | Done.  A forward declaration is enough for a field held through a *pointer* and not for one held **by value**, which needs a size; the SCC order is over all dependencies, so a group made cyclic by pointers is one SCC whose internal order is arbitrary, and that is where a by-value field lands ahead of its definition.  The by-value edges are acyclic -- `check_finite` says so -- and `PrintC.sort_types` emits a topological order of them, depth-first in the original order so the diff stays small.  `tests/custard/CByValue.fst`, which needs a *polymorphic* container to bite, a source bundle of mutual types being already ordered.  Separately, `Extract.binder_classes` returned `[]` whenever `lookup_sigelt` missed, and `[]` is a short-circuit rather than "all `Poly`": the whole spine goes through unfiltered, which is §18.1's miscompilation reached by the fv path instead of the variable path.  It now falls back to `lookup_lid_typ`, the lookup `binder_flags` has always used, so the spine and the flags come from one declaration; inferred rather than reproduced, since neither we nor the reporter could minimize it.  And `PrintC.lookup_var` no longer prints a name it cannot resolve -- the karamel backend caught this IR defect only because its terms are De Bruijn -- rejecting through a new `reject_ir` that says the IR is malformed rather than that C cannot express it. |
| M10ξ | **A definition's arity comes from its lambda, and dead bindings do not reach C** (§19.4, §19.5) | Done.  `Mono.classify` reads a definition's binders off its *type* and `Extract.extract_letbinding` reads them off its *lambda*, and when an abbreviation stops the arrow spine short the two disagree -- the definition deletes an erased binder that every call site keeps passing.  EverParse's `jump_header : unit -> jumper parse_header` is five binders that the type shows as one.  Unfolding harder is not the fix: a refinement is not a `Tm_arrow` however much unfolding is allowed, and these step lists omit `Zeta` on purpose.  `Mono.classify_def` extends the classification with the lambda's surplus binders, filtered by `is_erased_binder` -- verbatim the rule `extract_letbinding` already applied to them -- so `split_mono_args`, `call_unit_flags` and `call_type_args` all agree with the definition, and the two sides come from one list instead of two that usually coincide.  A no-op wherever the spine is already complete.  This supersedes the M10ν `lookup_sigelt` diagnosis, which the reporter's instrumented build disproved: the lookup never misses and the classification is short, not empty; the fallback stays because a short-circuit indistinguishable from an answer is worth closing regardless.  Separately, `PrintC` drops an `ELet` whose name the body never reads when the initializer is pure, which is what a pattern match using none of its fields leaves behind and what `-Werror=unused-variable` refuses; in the printer rather than `Simplify` because it is a fact about C.  `tests/custard/EraseAbbrev.fst` (checked to fail without the fix, emitting `add5 () x () 6`) and `tests/custard/CDeadLet.fst`.  The 6m20s whole-module profile also arrived and §18.3's explanation was wrong: `Extract.norm` is 374.7s of 380s and the growth is in per-call cost, not call count, and is sub-additive in roots. |
| M10ο | **A normalizer returns a meaning, not a tag; and a cell written but never read** (§19.7, §19.8) | Done.  The reporter found the root cause of §19.2 himself and it is one line: `norm` unfolds `jumper parse_header` into exactly the arrow that was wanted, wrapped in a `Tm_ascribed`, and `SS.compress` does not strip an ascription, so `| Tm_arrow _ ->` never fired and the spine stopped one abbreviation short.  His tag census over one `jump_header` run says this is the common case and not a corner: six arrows behind an ascription, twenty-four refinements behind one.  So the fix is generalized rather than local -- `Mono.strip` alternates `unascribe` and `unrefine` to a fixed point, and no shape test in `Mono` reads a tag without it (`is_arity_aux`, `is_star_aux`, `arrow_formals_unfold_aux`), nor do `Extract.peel_typ` and `Extract.is_prop_sig`.  The failure mode is why: reading a tag off a wrapper answers "not an arrow" and "not an arity", and both are wrong in the direction that miscompiles.  Generalizing found a second instance and a trap: `peel_typ` matched on the *stripped* term but then called `U.arrow_formals_comp` on the unstripped one, which yields zero binders, so `peel_typ (n - 0)` recursed forever -- `Effects.fst` hung for minutes with no budget error at all, which is the signature of a Custard-level loop rather than a big reduction.  Stripping for the match is not enough; the term has to be rebound.  This also supersedes M10ξ's claim to be the EverParse cause: `classify_def` cannot fire there, because the declaration comes from an interface and `lb.lbdef` is `Tm_unknown`, so there are no surplus binders to read.  It stays, with a real single-file reproduction.  With the ascription fix, whole-module direct-to-C of `CBOR.Pulse.API.Det.C` succeeds, the 3419 lines compile under `gcc -Wall -Wextra`, and all 57 entry points extract individually.  The two remaining `-Werror` blockers are also closed, both in `PrintC`: §19.5's dead binding now uses `is_droppable` rather than `is_pure`, since a read of a collapsed cell cannot *move* across a write but can always *go*; and `cell_dead`/`drop_writes` delete a one-cell allocation every occurrence of which is the target of a write, which is what Pulse's `fn while` measure erases to.  `Goto_test1` goes from six lines to one.  Reverted with these: the ulib `inline_for_extraction` on `fst`/`snd`, which changed standard ML extraction repo-wide for a cosmetic Custard gain (§19.8a). |
| M10π | **A redundant alias, and a specification named as an entry point** (§19.10, §19.11) | Done.  The `_letpattern` that survived M10ο is not a dead binding -- the name *is* read, by the match that scrutinizes it -- so the reporter dumped the IR instead of guessing, and the answer is that `emit_match` takes the direct path on a stable scrutinee, emits no read of it, and binds the branch's fields with `bind_alias`, which emits nothing when the body does not use them; the declaration is left with no users at all.  It is a **redundant alias**: `let x = <stable expr> in e2` declares a second name for a value this backend never assigns to, and `bind_alias` is already the answer to that everywhere else in the printer.  No side condition beyond `is_stable`, which is the licence `emit_match` has always taken.  The live cases collapse too, which is most of the value: `Pulse_Lib_HashTable` loses four copies of a function pointer and `Example_Slice` a pointer copy, and `_letpattern` bound to a plain variable appears 335 times in EverParse's output.  Separately, `--custard_entry` on a separation-logic predicate -- `cbor_det_match : perm -> cbor_det_t -> Spec.cbor -> slprop` -- was rejected with error 368 for the recursive datatype `Prims.list`, which is true about `Spec.cbor` and no answer at all to what was asked: the result is `slprop`, the index is ghost, and nothing in the program holds one.  `--custard_entry_module` already declined to root these (`erased_definition`); an explicit root was taken at its word, which is defensible until the word is `slprop`.  `Extract.root_is_erased` now asks before requesting, and reports rather than skipping, on the same reasoning that makes a misspelled entry an error.  The predicate is deliberately *not* `erased_definition`, and two rounds of the suite said why: `must_erase_for_extraction` answers yes for `unit`, so the effect has to be total or ghost as well (`main : unit -> ML unit` returns nothing and is the whole program), and a *type* is exempt outright, since its result is `Type` and a type abbreviation named by `--custard_entry` is exactly what a hand-written realization needs emitted (`TypeEntry.fst` caught it).  `tests/custard/pulse/PulseSpecRoot.fst`, the suite's one negative test and so a rule of its own. |
| M10ρ | **A lambda without a name, and a proposition nobody asked about** (§19.12, §19.13, §19.14) | Done.  Three findings from the CDDL half of the reporter's corpus, and the first is the reporter's own bisection: Custard already emits function pointers in structs exactly as karamel does, so the entire gap between `FunPtrRecord.fst` (works) and `CDDL.Pulse.AST.Det.C.cbor_det_impl` (error 368) is that the second writes its functions inline.  A closed lambda is a function nobody named; `Simplify.lift_lambdas` names it, before `dce` so the new declarations are in the call graph and before `scc` so they are ordered, inheriting the enclosing declaration's type parameters so free type variables cost nothing.  C only -- OCaml has closures and karamel has its own treatment.  Nobody writes these by hand: all eleven come from an `inline_for_extraction` record of thunks whose fields beta-reduce, against nineteen bare names that already worked and ten erased ghost fields.  A lambda that still reaches `PrintC` therefore genuinely captures, and says so.  Second, the advice attached to a type-variable rejection recommended `--custard_monomorphize_types`, which the reporter had set; `PrintC.mono_advice` asks first, and reports a Custard bug when the flag is already on, because advice that names the reader's own command line is worse than none.  Third, error 365 exhausting 10^9 steps "normalizing a type signature" on `env9 : bundle_env ... { bundle_env_included ... /\ ... }` -- a machine-generated CDDL well-formedness proof, which `is_type_sig` normalized whole and then discarded.  Both `is_type_sig` and `is_prop_sig` now `Mono.strip` first; `Mono` was already right, since `is_arity_aux` never lets a `Tm_refine` reach its normalizer.  `tests/custard/RefStrip.fst` is a 2^40-step proposition in a refinement under a 20000-step budget, and the reproduction that does *not* work is worth recording: a recursive function in the refinement is never unfolded by this step list, so it has to be a chain of abbreviations. |
| M10σ | **`Pulse.Lib.Slice` compiles to a Rust slice** (§19.15, §20) | Done.  karamel recognizes a slice by name and Custard's monomorphization erased the name, so every borrow became an owning `Box` and the reporter's program read back zeroes -- a miscompilation, not a build failure, which is why the test runs the Rust binary and checks its own answers.  `--custard_backend Krml` splits into `KrmlC` and `KrmlRust`, because the two want *different programs* and no property of the F\* source distinguishes them; `tests/extraction/backends` had already had them as separate rows passing identical flags.  A new `Modelled` decl flag, deliberately not `Realized`: a realization is hand-written OCaml and its declaration is still Custard's to emit on the karamel path, a model is the target compiler's and never is -- sharing the flag deleted `FStar.Pervasives.Native.tuple2`.  Only the *type* declaration is dropped; the operations stay as externals, since karamel's checker resolves every reference before the Rust pass rewrites any of them, and their type variables print as `TBound` rather than the usual external's `TAny`, Rust having no cast from `any`.  `FStar.Pervasives.Native.tupleN` is modelled too on that backend and prints as the IR's long-unused `TTuple`/`ETuple`/`PTuple`, because `split` becomes `split_at_mut` and `OptimizeMiniRust.retrieve_pair_type` *crashes* on a struct; `krml -fkeep-tuples` is not optional for the same reason.  `Builtins.is_known_krml_model_op` whitelists the seven operations `AstToMiniRust` actually matches, so a future runtime `val` in a modelled module is rejected here rather than by rustc.  `tests/custard/pulse/PulseSlice.fst`, compiled and run on both columns; its C column needs `--custard_monomorphize_types`, a pre-existing limit unrelated to slices (§20.5). |
| M10τ | **A projector whose field is a function** (§21) | Done.  Master's #4389 makes projectors and discriminators declaration-only, so `Extract.assumed_projector_lb` -- written for `[@@no_auto_projectors]`, and until now reached by almost nothing -- became the path every projector takes, and it took the projectee to be the *last* binder of the projector's type.  `U.arrow_formals_comp` flattens the whole spine, so when the projected field is itself a function the last binder is the field's own argument and the synthesized match scrutinized that: `i.impl_validate i.contents` came out as `i.contents.impl_validate`.  A miscompilation rather than a rejection, and it surfaced three modules away as a C field with no owner, a Pulse constructor with no type, and an OCaml type error in generated code.  The projectee is now the first binder headed by the inductive the constructor belongs to; the trailing binders are kept and the match applied to them, which is the shape F\* used to generate and the one `Simplify.eta_reduce` exists for.  `tests/custard/CFunPtr.fst`, `MonoHoles.fst` and `pulse/test`'s `Example.Hashtable` all reproduce it.  Also `FStar.Tactics.MkProjectors`, deleted by the same merge, removed from `src/custard/entrypoints.txt`. |
| M10υ | **A discarded value's name, and a slice in a returned struct** (§20.6) | Done.  Round 9 of the EverParse report: 436 Rust errors down to 28, miscompilation gone, and two of the remaining classes worth chasing.  `PrintKrml` named the binder it invents for a discarded `ESeq` component `_`; karamel's use analysis rewrites an unread binding into `let b = e1 in ignore b`, and its Rust backend prints a binder's name verbatim, so the reference came out as `ignore(_)`, which is not an expression in Rust.  Now an ordinary name, freshened against the scope because `find` takes the first match and `Rename` gives a local its bare source spelling.  The other is karamel's, and the report's reading of it was off: `AstToMiniRust` has no path from a slice to a `Box`, so a field emitted as `Box<[T]>` held a *buffer* and the two types were not structurally identical after all.  The real defect is the `E0106`s: karamel sorts a pointer-holding struct into returned (own them, `Box`) or not-returned (borrow them, lifetime), and a slice fits neither, so a returned struct with a slice field gets `box=true, lifetime=false` and emits `&[T]` in a type binding no lifetime.  `tests/custard/pulse/PulseSliceRec.fst` reproduces it in three declarations and one total function; `krml -fno-box` is the workaround the test uses.  Reported as karamel#753. |
| M10φ | **Operators get their names changed underneath us** (§22) | Done.  Merging master brought uniform operator mangling: `( + )` is `op_Plus`, `( .() )` is `op_Dot_Lparen_Rparen`, and `op_Minus` now means binary subtraction rather than negation.  Custard reads those names in `Builtins.prims_rule` and the `Pulse.Lib.Vec`/`ArrayPtr` rules, and writes them in `PrintOCaml` and to karamel, which still spells them the old way; `Builtins.krml_compat_name` is the twin of master's `FStarC.Extraction.Krml.krml_compat_name` and is applied in `lident_of_name`, before the specialization suffix, so that references and declarations move together.  Master's table was missing `op_Star`, the one Prims operator whose old name is not derivable from the new one by the same rule as the rest; adding it fixes FINDINGS.md #6 in both the C and krml C columns.  Separately, `Pulse_RuntimeUtils.ml` now calls a *discriminator* by OCaml name, and a discriminator is `Inline` and never emitted -- so `Extract` records roots before marking and does not inline a rooted one, and `Simplify.inline_decls` keeps an `Inline` declaration that is also `Root` (§22.2). |
| M10χ | **Custard's error codes moved up by one** (§22.1) | Done.  Master assigned 362 to `Error_AmbiguousName` while this branch already held 362-369, and 362 is not free to move: `tests/overloading/strict/StrictDuplicate.fst` demotes it with `--warn_error +362` and the book names it by number.  A published number outranks a branch-local one, so Custard's codes are now **363-370**.  The numbers in `FStarC.Errors.Codes.fst` are explicit rather than positional, so this is a relabelling; what it touches is every place a number is spelled out by hand -- the `CODE_*` variables the suite greps for, the `--warn_error @367` of the `--custard_warn_any` tests, two comments in `PrintC` and `Extract`, and the prose of sections 18 through 21.  Numbers cited in older bug reports are one lower than the ones the compiler now prints. |
| M10ψ | **"It compiles" is not an acceptance criterion** (§23) | Done, from #4482.  Every backend test until now asserted a golden file or a clean compile, and section 19.15 is the proof that neither is a specification: karamel compiled a borrowed slice as an owning `Box`, writes through it were discarded, and nothing failed because nothing ran anything.  Two reduced deterministic-CBOR checkers now do -- `tests/custard/CborBoundary.fst` over a `ref`-linked list, which needs no Pulse and so runs under stage1 and stage2 too, and `tests/custard/pulse/CborBoundarySlice.fst` over a `Pulse.Lib.Slice.slice byte`, which is what EverParse's parsers take and the only one that drives the Rust column.  One corpus of 48 boundary vectors, one independent Python oracle, one adequacy script, all in `cbor-corpus/`; the two copies the PR arrived with were byte-identical and free to drift.  The result worth keeping is the measurement, not the test: greedy set cover over *line coverage* shrinks a 12,110-input corpus 400x with **identical coverage and 13% fewer mutants killed**, while reducing against mutants reproduces the full corpus on a held-out family it was never fitted to (152/152 against 57/152 at the same size).  Coverage is not the signal to minimise against.  Sanitizers are on by default, since one mutant was otherwise detected only when binary layout made its memory unsafety observable.  Also `_test_pulse` now runs `tests/custard/pulse/`, which `make ci` reaches through `test-3` -- until this change the entire Rust column, section 20.6's `Box` regression included, guarded nothing (§23.3). |
| M10ω | **The unit is a header and a source** (§24) | Done.  The direct-to-C backend wrote one file, everything in it had external linkage, and there was no declaration of anything for a caller to include -- so calling an extracted function meant writing its prototype out by hand, and linking two units risked a duplicate symbol for every shared name.  `print_program` now returns a header and a source, and the driver writes `<stem>.h` beside the source.  The flag that decides storage is not a new one: the IR has carried `Private` since M2 and `PrintC` read it, but **nothing ever produced it**, which is why nothing was ever `static`.  Storage now comes from `Root`, which already means what we need -- a declaration is a root because `--custard_entry` named it, and naming a root is exactly the claim that a caller Custard cannot see will call it.  The `Entrypoint` is excluded because `--custard_main` makes its target a root only to keep it alive through DCE, and the generated `main` calls it from the same file.  The header carries the unit's whole type language rather than a reachability-trimmed subset -- `struct` and `typedef` have no linkage, so emitting all of them collides with nothing, while trimming buys "field has incomplete type" at the first include -- and only the public prototypes, since a prototype *is* the linkage claim.  The source includes its own header, which is what makes the header checked rather than merely shipped.  On DICE 144 declarations become `static` and the six `--custard_entry` names are the six that do not; `tests/custard`'s greps now cover both files, and `pulse/test` gained ten `*.h.expected` goldens. |
| M10αα | **An argument goes missing between two definitions** (§25) | Done.  Round 19 of the EverParse report reduced everything still blocking CDDL to one eleven-line module.  `let g : bool -> bool -> bool = f` is parameterless in the source and arity two in its type; `g` itself was eta-expanded correctly, but its *callers* were not, and `let call_g a b = g a b` came out one parameter short, calling `Wrap_g(a)` -- "too few arguments" against a prototype the same run had emitted.  The sharp part is that `call_g` and `call_g_partial` produced **byte-identical C** although one is a full application and the other partial: an argument went missing, and the IR was wrong before the backend saw it.  Two correct passes: `eta_reduce` shortens `fun a b -> g a b` to `fun a -> g a`, and `eta_expand` exists to undo that for C -- but it bounded expansion by a table of arities computed once, from the program as it found it, so it read `g` as arity 0 while the same sweep was giving `g` its two binders.  The table was stale by exactly one link, which is why the control `call_f` was clean.  `eta_expand_decls` now runs to a fixpoint; each round can only add binders and never more than `arrow_arity dl_ret`, so it terminates.  Separately, `PrintC` printed `EApp` without ever asking the callee's arity, which is why this reached a C compiler instead of a diagnostic: it now records every arity and refuses a mismatch -- under-application as 368 with the `[@@@monomorphize]` remedy named, over-application as the malformed-IR refusal.  `CEtaChain.fst` (four links, so one round cannot pass it) and `CLamField.fst`.  Not fixed, deliberately: a definition whose body is a call returning a function stays a global variable, because expanding it would re-evaluate the call at every use (§25.3). |
| M10ββ | **A green result that is not evidence** (§23.4) | Done, from #4484.  Section 24's `#include "<Module>.h"` meant the generated source no longer compiles from a directory other than the one extraction wrote it to, and `mutants.py` builds each mutant in `_output/mutants/`.  Every mutant became uncompilable and both adequacy figures collapsed to `killed 0 / 0 (uncompilable 46)`.  The include path is the trivial half; the half worth recording is that **the script did not error out** -- `killed 0 / 0` is a pass under any "did it fail?" reading, so the study would have gone on reporting success while measuring nothing, which is section 23's own thesis pointed at section 23's own tooling.  The uncompilable count is now fatal rather than reported, as is a zero-mutant run: an uncompilable mutant is an absent test, not a weak one, and it is always a defect in the script or the backend, never a property of the corpus.  Verified both ways -- the guard exits 1 on the broken include path and 0 once fixed, and the four figures return to 46/46, 46/46, 48/49, 46/59. |
| M10γγ | **Two more ways to lose an argument** (§26) | Done.  Round 20 found two arity defects section 25's check did not catch, one of which it *had* caught in a different program.  (1) `let e : bool -> bool -> bool = ap band` is lowered to a **variable** of function-pointer type, because §25.3's `cheap_expr` guard declines to expand a body that computes before returning a function -- and both the arity table and the new check recorded *definitions*, keyed on binder count, so both read `e` as arity 0 and `call_e` stayed eta-short.  The variable/function lowering turned out to be load-bearing for correctness: becoming a variable is what made the callee invisible.  Both tables now read a parameterless arrow-typed definition's arity off its **type**, which is what the emitted object accepts.  (2) `Extract`'s `peel` consumes one arrow per extra lambda binder and called `head_ty` **once, on the way in**; `eq_test` unfolds to one arrow whose codomain is another abbreviation hiding the second, so peeling two binders consumed one arrow, landed on a name and stopped, while both binders were emitted -- a definition declared to return `bool -> bool` over a body of type `bool`.  It now unfolds at every step, like its term-level twin `peel_typ`.  Worth noting on severity: gcc 13 accepts that with `-Wint-conversion` and prints the right answer because a `bool` round-trips through a pointer on that ABI, while gcc 14 rejects it -- right only on the compiler it was tested against.  `CVarArity.fst`, `CAbbrevArity.fst` (which is `CDDL.Spec.EqTest.eq_test` verbatim), and `CPartialCall.fst` for the check firing on a *local* partial application, which eta-expansion cannot reach.  Both defects are the same mistake at different scales: an arity read off the wrong representation (§26.4). |
| M10δδ | **A constant function compiled to mutable state** (§27) | Done.  Round 21 confirmed both §26 fixes and got the real CDDL combinator library extracting and running, and left one finding: a pure, total, compile-time-constant function was being lowered to a `static` function pointer assigned in `custard_init_globals`, which makes skipping the initializer a null-pointer call from a *public* entry point rather than a wrong answer, and puts an indirect call on the hot path.  The blocker was not §25.3's `cheap_expr`, which already admits the body, but the arity bound in `eta_expand_decl`, which only fires on an under-applied head.  Relaxing that bound as proposed would be unsound as a performance matter -- `build_table 1000000` is a known top-level function with cheap arguments, so `let table : int -> int = build_table 1000000` would be re-evaluated per call -- so `Simplify.reduce` instead gains a rule that *removes* a call: a **forwarder**, a pure non-recursive definition whose body is exactly one of its own binders, applied to all its arguments reduces to that argument.  `id_fn band` becomes `band`, which the existing `EQual` case of `eta_expand_decl` expands into a real `static` function; `id_fn` dies in DCE and `custard_init_globals` is not emitted.  `tests/custard/CInitTrap.fst`, whose second forwarder returns its *second* binder.  Four existing tests contained an incidental forwarder and were rewritten to use their arguments rather than return one (§27.5); all five suites, the DICE example, and all four CBOR mutation-adequacy figures are unchanged |
| M10εε | **A divergence the budget was for** (§28) | Done.  #4494 reports the legacy pipelines allocating without bound and being OOM-killed on a type computed by a recursive definition that makes no progress when unfolded, and asks for a step bound as the broader fix.  §3.6's budget is that bound, and this measures it: the same reduction is `Fatal error: allocation failure during minor GC` under `--codegen OCaml` and error 365 -- naming the term and the request chain -- under Custard, because `norm_bounded` was applied to *type* normalization and not just to specialization keys.  Demand-driven extraction (§3.2) is a second and weaker guard, since the report's own reduction has the offending definition dead; `tests/custard/TypeDiverge.fst` therefore names it with `--custard_entry`, and spells the recursion out rather than importing `false_elim` so that it survives #4494 marking that `irreducible`.  Separately, `false_elim` had no builtin rule, so Custard extracted its non-terminating *definition*: an infinite loop where OCaml wants a `failwith`, and on C a hard 368 about the return type of a function that never returns.  `Builtins.pervasives_rule` gives it the `EAbort`/`TAny` treatment `magic` and `admit` have had since M2; `tests/custard/CFalseElim.fst`.  The dispatcher branch has to *fall through*, since `FStar.Pervasives` is also a realized module -- shadowing it cut `Mkdtuple3` off from `is_realized_module`, which `Realized.fst` caught |
| M10ζζ | **Integer literals change representation underneath us** (§29) | Done.  A master merge replaced `Const_int of string & option (signedness & width)` with a value plus the base it was written in, and split machine integers into `Const_machine_int`.  Custard's IR is unchanged, so the work is three boundary cases that want different answers: `constant_of_sconst` keeps the source spelling via `string_of_int_literal`, matching the legacy ML extraction; `key_of_const` must use the *value*, since `eq_const` ignores the base and a key that kept it would specialize `f 16` and `f 0x10` twice; `hint_of_term` is cosmetic.  The merge also canonicalized hex to lowercase without leading zeros, which nothing pins -- except `cbor-corpus/mutants.py`, whose `byte+1` family required `[0-9A-F]{2}` and so silently generated ten fewer mutants, reporting 36/36 where it had reported 46/46.  Every mutant killed before was still killed; the denominator moved, which is §23.4's lesson in a second form.  Pattern widened; all four figures back to 46/46, 46/46, 48/49, 46/59.  Also: `no_auto_projectors` is a deprecated no-op, so `AssumedProj.fsti` drops it, and both §28 tests survive #4494 marking `false_elim` `irreducible`, which is what they were written for |
| M10ηη | **A function that returns a function pointer** (§30) | Done.  Round 22 withdrew round 21's framing -- a function pointer in a record is fine -- and reduced the CDDL blocker to two narrower bugs.  The first is the fourth of the §25/§26 arity family and the first the pass *causes* rather than misreads: a one-field record collapses (§5.2), so `mk_arg (x: U8.t) : fixedb` has type `u8 -> (u8 -> usize)`, §25 sees a result type that is still an arrow and gives it a second binder -- rewriting the definition and none of its call sites, which were already saturated at one.  A function returning a function pointer is ordinary C and needed nothing.  Expansion is now capped by a per-round table of the fewest arguments any use supplies, counting only uses this pass cannot itself grow: the head call of an expandable body can, so `call_g_partial` does not pin `g` and `CEtaChain`'s chain still resolves, while `mk_arg`'s use under a `let` does.  `tests/custard/pulse/PulseFnPtrRet.fst`, run.  The second bug is not fixed and is not an arity defect: a `Type0` *field* whose siblings' types depend on it is an existential package, not an instance of a parameterized type, so §6 does not reach it and the sibling degrades to `any -> usize`.  Promoting the field to a parameter is a feature at §6's scale, and §30.3 records why the inline case must not be papered over |
| M10θθ | **A field projection is not a type constructor** (§30.4, §30.5) | Done.  Round 22's second bug, reduced with an MWE carrying CDDL's actual shape -- a bundle built by structural recursion over a grammar derivation.  Specialization already does its half: with the derivation and the bundle arguments `[@@monomorphize]`, the recursion unrolls and every combinator is specialized per bundle *value*, so at each construction site the record is concrete.  The type was still `any` for an unrelated reason -- a projector is not a type constructor, so `ty_of_typ` fell through to `ty_of_fv` -- and reducing it is a third case of the kind that file already has two of, with the scrutinee unfolded by delta since the record is as often a top-level name as a literal.  Every specialization's interior is now ground; `tests/custard/CTypeField.fst`, run.  What is left is exactly §30.3 and no longer more than that: the record's own declaration collapses to `any -> usize`, and fixing it means §6 keyed on a `Type0` *field* rather than on a type argument -- bounded work now, because the value to key on is what this made available.  Also §30.4: `[@@monomorphize]` on a constructor field is read by nothing, which is now warning 371 rather than silence, and 364 no longer advises writing it somewhere that does not exist |
| M10ιι | **A recursive builder, and a declaration that lost its type** (§30.6, §30.7) | Done.  Round 23 reduced §30.3 to one line of difference: an `unfold` bundle builder works, a `let rec` one does not, because only the latter survives extraction as a value.  Two fixes.  §30.5's reduction now needs `Zeta` to see through the recursion, and `Zeta` can exhaust the budget -- so `norm_optional` lets *this* reduction give up and fall back to `TAny`, on the principle that a normalization the program's meaning depends on must fail loudly and one that only sharpens a fallback must not.  That grounds the uses.  The builder itself was the rest: a record collapsing to a field of its own erased `Type0` field is declared `any` however concrete each specialization is.  `Simplify.narrow_rets` reads the result type back off the body, after `records` and as a fixpoint over the call chain, rewriting only signatures -- `coerce_prog` re-derives each use from the signature, so the coercions between them vanish.  This is §30.3 closed, and without §6 keyed on a field, which turned out not to be needed.  `tests/custard/RecTyField.fst`, run, no `any` emitted |
| M10κκ | **The same field, spelled three ways** (§30.8, §30.9) | Done.  Round 24: §30.5 and §30.7 had fixed the one spelling EverParse does not use.  CDDL reaches a bundle's `Type0` field through a `match` (Error 364, the field becomes a variable) or through an accessor (Error 368, the bundle becomes a runtime binder), never through a projection.  Three fixes, all narrow.  `specialize` resolves a match on a *type-storing* constructor by unfolding just those scrutinee heads, with `Zeta` on for them alone and permitted to give up (§30.6) -- the first trigger was too loose and fired on every `option`, which is why the check is "a type the constructor stores", past the inductive's parameters.  `ty_of_typ` runs the same reduction as a fallback once `ty_of_fv` has given up, so an accessor and a projection behave alike.  And rule 4b: a binder of a type-carrying inductive is `Mono` unasked, because the alternative is not a slower program but no program.  `FieldAttr` accordingly loses its 368 and pins warning 371 under `--warn_error`; `coerce_prog` writes the recovered type back into local `let` annotations.  `tests/custard/RecTyAcc.fst`, run |
| M10λλ | **Opt-in compile-time evaluation** (§30.10) | Done.  Round 25's blocker and the first feature in this stretch that is a design decision rather than a repair.  `CDDL.Pulse.AST.Literal.string_length` is `length (list_of_string x)` applied only ever to literals; compiling it asks C for a `list char`.  Custard will not evaluate closed terms on its own initiative -- that is a licence to unfold anything, and the output stops resembling the input -- so the decision is the author's, one definition at a time: `[@@custard_compile_time]` means every application is evaluated during extraction, with delta, `Zeta` and `SafePrimops` all on.  The promise is checked, and the obvious check is wrong: testing the *reduct's* head passes exactly the failing case, because unfolding removes the head whether or not anything was computed.  The test is on the application as written -- free names -- so error 372 names the definition and the variable that made it impossible, rather than falling back to compiling a `list char` into C.  The attribute belongs on the outermost definition whose result is representable, since a marked definition's own type is never compiled.  `tests/custard/CompileTime.fst` (run, C reads `uint32_t len = 5U`) and `CompileTimeBad.fst` (pins the 372) |
| M10μμ | **A compile-time demand, and three per-term-size costs** (§30.11, §30.12) | Done.  Round 31.  §30.10's attribute did not reach CDDL: `impl_literal` destructures a literal and hands the *string* it finds to the marked function, so the argument is a pattern variable and 372 fires; annotating the binder just moves the error one level up, which is the treadmill rule 4b exists to end.  Rule 4b cannot help, and the reason matters -- it is keyed on a constructor storing a *type*, justified by there being no runtime representation at all, and a `string` has a perfectly good one.  So rule 4c is a demand read off the *body*: a binder an application of a `custard_compile_time` definition depends on, directly or through the match that binds what it is applied to, is `Mono`.  Reported as binder *positions*, because `classify` opens the arrow and the body opens the lambda and the first attempt matched `bv` identity and silently never fired.  `tests/custard/LitStr.fst`, no annotations, run.  Separately, round 31 sampled the blow-up under `gdb` and found three per-term-size costs, none of them a specialization count (643 total, max 8 per definition): `closure_as_term`'s universe erasure is a full deep copy charged as *one* budget step, which is why no budget ever bounded the hang -- it now charges per node; `Env.disc_proj_info` is four uncached `lookup_qname`s on every projector reduction, now memoized; and `key_of_term` built megabyte keys with left-nested `^`, now linear.  Also `Driver.run` reports its profile on the error path, since a failing run is the one worth profiling and `Universal` reports only after a file type-checks |
| M10νν | **A local that captures a top-level name** (§30.13) | Done.  Not from a report: `make custard` broke on master's real-literal rewrite, whose `try_mk (mantissa exponent : int)` shadows the projections it calls.  F* is untroubled; the emitted OCaml refers to a same-file top-level *unqualified*, because inside `Foo` there is no way to write `Foo.bar`, so the local captures it and the result either does not compile or compiles against the wrong binding.  Locals are renamed rather than references qualified -- a local's name means nothing outside its definition, and a top-level name is what a realization may be written against.  `reserve_top` runs with `current_module` already set, since whether a declaration is spelled with a qualifier is the whole question, and the first attempt collected mangled names for that reason.  Record fields and type variables deliberately keep the old spelling: a field has to match a declaration this run may not own.  The same run found two roots of §4.4's other kind, both called only from the hand-written menhir grammars in `src/ml` -- `FStarC.Real.of_string`, `FStarC.Const.parse_int_literal`, plus the abbreviation `FStarC.Real.real`, which is unfolded unless named |
| M10ξξ | **A parameter nothing observable depends on** (§30.14) | Done.  Round 32.  §30.12 turned the hang into an error and the error named the term: a CDDL type signature of 9,012,230 bytes *before* reduction, reached through `bool`, made of 6995 `Ghost.reveal`, 4668 refinements on `cbor` and 990 `serializable` -- in which `impl_serialize`'s specification argument occurs exactly once, inside a `pure (...)` in a postcondition, while the compiled signature is three names.  So the fix is not to reduce it faster.  Rule 8: a `Mono` binder absent from the body *and* from the observable part of the rest of the type -- refinements replaced by what they refine, computations by their result, which are the two places a specification hides -- is `Dropped`, removing a specialization and changing no signature, because a `Mono` argument was never passed at run time.  The body test is what makes it sound (`if n = 0` mentions `n` nowhere in the type), the body has to be the one `extract_as` supplies (`Anf.tick` specifies `fun s n -> n` and prints `s`), and a type may have more binders than its lambda (a `class monad` projector is four abstractions over an arrow of six -- reading those as absent deleted `mbind`'s first argument).  Confining it to `Mono` is what makes it free: `RetArity.f`'s unread `frame` and `post` are `Poly` and are part of its ABI regardless.  On round 32's measurement the cost removed was linear in the argument and entirely specialization -- 517 ms `norm`, 355 ms `split_mono_args`, 302 ms `key` for a 25600-element list contributing `return u;` -- and extraction is now flat at 0.55 s.  `tests/custard/DeadMono.fst` extracts under a budget four orders of magnitude too small to normalize its argument.  §30.12's accounting also changed what a budget *is*, and CDDL now needs `--custard_norm_budget 100000000`; the default stays at 10^7 anyway, because raising it to 10^8 makes `TypeDiverge` overflow the stack instead of reporting error 365, and a budget that fires after the normalizer runs out of stack is not a budget |
| M10οο | **A name that doubles at every level** (§30.15) | Done.  Round 33, which also retracted round 32's central number: the term is 270 bytes, not 9 MB -- the 9 MB was the *chain*, whose frames are specialization instantiations, so what was 8 MB is a **name**.  `Monomorphize.hint_of_cty` rendered a type structurally with no bound, and `TApp (n, [])` renders through `n.spec`, so an instantiation's name is built from the names of the instantiations it is made of and a type that nests doubles the name per level.  Bounded now in depth (4) and clipped to 48; truncation can only collide, and `request`'s `pick` already numbers a collision.  `Extract.fit` had the same hole from the other end -- it kept the first component "whatever its length" -- and truncates it too.  Two quadratic costs underneath: `FStarC_String.list_of_string` indexed with `BatUTF8.get`, which walks from the start, and `PrintC.sanitize` called it three times, twice to read one character.  Both are on the path of every name Custard prints.  On the 25-line reproducer at depth 12: 159 s to 14.9 s, C output 1,237,635 to 23,318 bytes, longest identifier **57,361 characters to 82** -- the width bound is the one that matters, since C99 promises 63 significant characters for an internal identifier and 31 for an external one.  `tests/custard/NameWidth.fst` |
| M10ππ | **An eta-reduction with nowhere to put the argument back** (§30.16) | Done.  Round 33, reported in passing.  `let consume (i: sig_t s) (u: U32.t) = i u`, where `sig_t` unfolds to an arrow, reached C as Error 368: it takes 1 argument and is applied to 2.  Eta-reduction shortened it to `fun i -> i` correctly, and eta-expansion -- the pass whose whole job is putting that argument back for C -- did not fire, because it reads what is still owed off the *head of the body*, and this body has no head.  It is a bare parameter, so `head = None` meant `missing = 0`.  There is no callee arity to read, but there are call sites, and the only reason to expand a headless body is that one of them supplies more arguments than the definition accepts -- exactly the condition C rejects.  The demand is read off `use_arity`, bounded by the result type's arity as every other case is, and zero when no caller asks.  `tests/custard/EtaVar.fst` |
| M10ρρ | **A value that is small only because it is shared** (§30.17) | Done.  Round 34.  `bundle_signoutputargs` is not diverging: at ten times the budget it runs ten times as long, allocates linearly to 59 GB, and reports a byte-identical error.  It is copying.  The term binds its predecessor once and reads five fields off it, so it is linear as written and doubles at every level once iota substitutes the binding away -- and producing a specialization key is exactly that substitution.  A key only has to *distinguish*, though, and merging is the only direction that can be wrong; so `split_mono_args` now falls back from the full normal form to the weak head normal form to the argument as written, warning 373 saying which.  Keying on a name preserves the sharing that reducing it destroys.  Error 365 at a `Mono` argument goes with it: termination is undecidable, the proxy for it is useless (`add_mod` reaches `pow2`, so `LetShare` answers the same as `spin 0`), and declining to reduce is well defined for both -- `NormBudget` now records warning 373 and extracts a program that diverges when run, which is what it says.  The divergent *type* of `TypeDiverge` has no as-written form and is still error 365.  `tests/custard/LetShare.fst` goes from Error 365 to 3.5 KB of OCaml at a chain of 40, and prints the same number the 587 KB exponential form prints |
| M10σσ | **`normalize_for_extraction`** (§31.1) | Done.  Round 35.  EverParse puts `[@@normalize_for_extraction (nbe :: T.steps)]` on every definition its CDDL tool generates, which is why the krml backend never meets `validate_typ'`: F\* has unfolded it against the concrete AST before extraction starts.  Custard has its own front end and was ignoring the attribute, so it met the interpreter as written and reported, correctly, that a `list char` has no C representation -- a 368 downstream of a missing pre-pass.  `Extract.fixup_normalize_for_extraction` honours it next to `fixup_extract_as`: steps normalized first so `nbe :: T.steps` need not be a literal, `erase_erasable_args` set as the ML pipeline sets it, `normalize_for_extraction_type` for the type, §3.6's budget still applied, and cached by lid since `extract_lid` runs once per specialization.  `tests/custard/NormForExtraction.fst` asserts both halves: the interpreter and its AST vanish, and the one function outside the whitelist survives as a call |
| M10ττ | **A chain for error 368** (§31.2) | Done.  Round 35, reported twice as the thing that stopped the reader.  364, 365 and 373 print "Reached through" because extraction is demand-driven and the chain is the demand; 368 printed a declaration name and nothing else, and `Prims.op_Less` -- used everywhere, appearing nowhere in the output, absent from `--custard_dump_specializations` -- is unactionable on its own.  The backend has no request chain, but it has the call graph, and reachability from a root is the same information from the other end: `PrintC.record_parents` walks breadth-first from the roots so the chain is a shortest one, resolving a constructor to its type as `Simplify.dce` does.  `tests/custard/ListC.fst` |
| M10υυ | **"the pass did not reach it" was a guess** (§31.3) | Done.  Round 35.  The 368 for `FStar.List.Tot.Base.isEmpty@char` claimed monomorphization had not reached `Prims.list` and asked for a bug report.  It had.  `FStar.List.Tot.Base` is realized by hand in OCaml, so `isEmpty` is an external, so §5.0.1's rule 4 froze every type in its signature -- a clone would name something the realization does not define.  The message now names the external that froze the type and says why.  It does not change the decision: honouring `realized_modules` under a backend with no hand-written realizations is arguably wrong, but that touches every C and krml test and is recorded as the next thing |
| M10φφ | **`LetShare` was registered but never run** (§30.17) | Done.  Round 35.  `FLAGS_LetShare` and `GREP_LetShare` were set, but the `CUSTARD_TESTS += LetShare` line was missing, so nothing expanded to a target and `make` skipped it silently.  Caught by the reporter, not by the suite, which is the uncomfortable part: a test that is not registered passes |
| M10χχ | **A chain entry is a term** (§32.2) | Done.  Round 37.  §31.2's chain found the `Prims.op_Less` that had cost a whole round, on the first try — and then printed a 6,426,280-byte error block, of which 6,425,658 bytes were one "Reached through" line.  A chain entry is a specialization *key*, rendered by `string_of_key`, so it is as big as the term is; §30.15 bounded the name Custard *emits*, which is a different string.  `Extract.clip_chain_entry` bounds each entry to 200 characters and says how much it dropped, keeping the prefix because the lid comes first in a key.  `PrintC`'s chain is bounded the same way on principle.  `tests/custard/WideChain.fst` — a 16,372-character key and a 727-byte diagnostic — and every reject test now asserts its diagnostic is under 100 KB |
| M10ψψ | **The specializer does no work at all** (§32.1) | Done, as a measurement.  Rounds 36 and 37.  All four CDDL entry points extract from a stock EverParse tree in 11–19 s, and the generated C was executed against an independent decoder over 12,109 vectors with 0 mismatches, then re-run under ASan/UBSan over 10,392 malformed inputs with 0 errors.  The number that matters is 0/0/0/7 specializations against round 31's 643: §12.3's cost was never intrinsic, it was the interpreter arriving unreduced.  A controlled comparison — 76 `normalize_for_extraction` occurrences stripped, four configurations — puts annotations alone at 2 of 4 and the attribute at 4 of 4, and shows blanket `custard_compile_time` at all 98 `sem_attr` sites making things worse, because `sem_attr` and `custard_compile_time` are different predicates |
| M10ωω | **A public surface** (§32.4) | Done.  Round 38.  The objection to exporting names was that §30.15's specialization hints are hints; the answer is that a consumer does not want a specialization.  EverParse's COSE calls 44 `cbor_det_*` symbols across a translation-unit boundary, and Custard's whole-program output of `CBOR.Pulse.API.Det.C` already exports 43 of them with no hint and no collision suffix, because that boundary is monomorphic.  `--custard_c_no_prefix M` emits the public definitions of `M` — exactly `is_public`, and additionally checked to have `n.spec = None` — under their unqualified names, as krml's `-no-prefix` does.  Collision is error 374 rather than a silent suffix; a module that renames nothing is warning 375.  `extern "C"` guards are unconditional and go after the includes, never around them.  `tests/custard/Export.fst` is extracted twice, once standalone and once as a library, and `ExportUser.cpp` is compiled as **C++** and linked against it — strip the guard and the link fails, which is the assertion.  `tests/custard/ColB.fst` is the collision |
| M10αβ | **An external has no body** (§32.5) | Done.  Kuiper report.  `[@@@monomorphize]` on a binder of a `custard_extern` substituted the argument into nothing: the signature lost the binder, the argument was discarded, and the fixed C symbol never learned what it was.  The reported form did not compile; the form nobody reported — a *closed* argument, so no capture and no arity mismatch — compiled and silently never called anything.  Error 376 rejects a `Mono` *value* binder on an external.  A `Mono` *type* binder stays allowed: it is substituted into the signature, which is all a type argument is.  `tests/custard/MonoExtern.fst` |
| M10αγ | **Storing a type is not an existential** (§32.6) | Done.  Kuiper report.  Rule 4b's `ctor_stores_type` asked only whether a constructor stores a `Type0`, so `\| D : (ty:Type0) -> len:UInt32.t -> desc` — where nothing mentions `ty`, the field is erased, and what remains is one uniform `UInt32.t` — was rejected with error 364 for no reason.  The condition is dependence, which is what §30.4's prose already said: a *later* field must mention the stored type.  And where rule 4b is right, error 364 said only its consequence and gave two unavailable remedies; `Mono.existential_field` now names the constructor and field, states that no annotation changes it, and gives the remedy that exists.  `tests/custard/StoredType.fst`, `tests/custard/ExistAdvice.fst` |
| M10αδ | **A misattributed realization** (§32.7) | Done.  Kuiper report.  Error 368's advice for a type frozen by §5.0.1 rule 4 asserted the external was "a hand-written realization for the OCaml backend"; for a `custard_extern` it is a C symbol the program named, and the reader was sent after an `.ml` file that does not exist.  `frozen_by_target` records the symbol and the sentence names it |
| M10αε | **The header is the API** (§32.9) | Done.  Round 39.  §32.4's output was linked against the real COSE consumer — checked-in EverParse-generated `COSE_Format.c` plus OpenSSL, cross-checked against `pycose` — and signs, verifies, and verifies `pycose`'s signature, clean under ASan/UBSan.  A strip is sufficient; no rename map is needed.  The generated types are ABI-identical to the hand-written header (40/8, 80, 32, 32) and the renaming is purely nominal.  The gap it found: types were not renamed, so a consumer could call a function but not spell what it returned, which contradicts §32.4's own claim that the header is the public surface.  A named module's types and their constructors are now renamed too — `c_tag` goes through the same map, `struct_tag` follows from `c_name` — and `ExportUser.cpp` uses the type, a field and an enum tag across the boundary in C++ |
| M10αζ | **One pair of parentheses** (§32.10) | Done.  Round 39.  `c_expr` parenthesizes every operator application, so `if (...)` added a second pair; clang emitted `-Wparentheses-equality` 78 times on one generated file, and gcc `-Wall -Wextra` never mentioned it.  Not cosmetic — a consumer building with `-Werror` under clang could not use the output.  `is_group` checks that the leading paren is the one the trailing paren closes, so `(a) && (b)` is not stripped; `unparen` drops the pair and `negate` adds one only when the operand is not already a group |
| M10αη | **A body that is a lambda is not a closure** (§33.1, §33.2) | Done.  Round 40, from a second reviewer porting Kuiper -- a Pulse DSL for verified CUDA kernels, 396 modules, extracted today through karamel and a ~1200-line plugin.  `let go (k: U32.t) : U32.t -> U32.t = ap (fun x -> add_mod x k)` was rejected as a lambda capturing a local variable, when the variable it captures is `go`'s own parameter and `let f x = fun y -> e` is `let f x y = e`.  §25's expansion could not have done it -- it works by *applying* the body, and a lambda applied to a fresh variable is a redex rather than a parameter -- and refused to consider it at all, because §25.3 admits only a *cheap* body.  That list bounds work repeated per call, and evaluating a lambda performs none: the body is not run.  So absorption is separate and unconditional, and takes the *declared* codomain rather than the body's own type, which `make custard` is what says: with the body's type the extracted compiler does not build, because the coercion a reified `Tac` match needs is never inserted.  `cheap_expr` additionally admits `EFun` and `EOp`, which is what unblocks the other Pulse shape -- `eta_reduce` moves an `fn`'s trailing `r` into the result arrow and the call becomes partial.  `CLamDef.fst` |
| M10αθ | **An attribute is written on the lambda** (§33.3) | Done.  Round 40.  With both of the above fixed the specialization still did not happen, and deleting the attribute produced a byte-identical dump -- the failure mode with no evidence at all.  A classification reads binders off a definition's *type*; `[@@@monomorphize]` is written on the *lambda*; Pulse's `tm_arrow` goes through `mk_arrow_with_name`, which builds its binder with `attrs = []`, so for a Pulse `fn` the two disagree and rule 3 never fires.  Fixable in Pulse, and fixed here instead because the narrower fix is the more correct one: §19.4 already argues the lambda is the more faithful of the two lists, and this is that argument about a binder's attributes rather than about how many binders there are.  Unioned positionally rather than preferred, since a type can have binders the lambda does not.  `tests/custard/pulse/PulseMono.fst` needs all three fixes to compile and checks its own answer when it runs |
| M10αι | **A correct rejection is not a bug report** (§33.4) | Done.  Round 40.  §32.6 explained an existential type to error 364; Kuiper meets the same type as a field of runtime data and gets 368, which said "that is a Custard bug, please report it" about the existential of §30.3, correctly rejected.  A wrong explanation is worse than none, because it is acted on.  368 could not say what 364 says because by the time the backend sees the type the `Type0` field is erased and what is left is a `TAny` with no visible cause -- so the cause is carried rather than inferred, as an `Existential` type flag the extractor sets from `Mono.existential_of_lid`.  Nothing reads it to make a decision: the type is rejected either way, and the flag exists so the rejection can say why.  Looked up along the whole `Reached through` chain, since the type that lost its representation is usually a *field's* type and the existential is the record above it.  `ExistChain.fst`, and a new `NOEGREP_` hook so that the sentence this replaces is pinned as *absent* -- otherwise nothing notices it coming back |
| M10ακ | **A rule sees its arguments reduced** (§34.1) | Done.  Round 41.  Kuiper's host side hands a kernel descriptor whose constructor stores a `Type0` a later field's type mentions, so §33.4 rejects it with 368 -- correctly, and neither remedy applies: the stored type is not held, it is *used to build a type*, and the list of descriptors is heterogeneous on purpose.  But the descriptor is not runtime data either, it is `inline_for_extraction noextract` and a literal at every call site, so the place for it is a rule.  The blocking question was whether a `Rule_prim` sees a structure or an opaque reference, and whether the descriptor's type must have a C layout before a rule is consulted.  Neither: §8.2's table is consulted before the definition is looked up, arguments arrive *reduced* -- the whole record, `Prims.Cons` chain and all, with `0<u32>` and `false` in the same list -- and *pre-layout*, an `ECtor` rather than §6's `ERecord`, with type arguments already erased.  The 368 cannot fire because `Simplify.dce` removes the types the rule consumed before the backend runs.  So there is no ordering gap and Kuiper's host side needs no compiler change.  The other half of the answer is that `register_rule` was exported, documented and never demonstrated: `tests/custard/plugin/CustardRulePlugin.fst` is the worked example, wired into `make custard`'s existing `plugin` target as a third root, asserting the descriptor's three types are absent from the C and then compiling and running it |
| M10αλ | **A recognized attribute in an unrecognized position** (§34.2) | Done.  Round 41.  §33.3's bug had no evidence at all, and asked what would have caught it the reporter's answer is that "did it have an effect" is unanswerable but "was it read" is a bit.  That is still a change to every reading site; the cheap half is that Custard's attribute set is closed and each is read in exactly one kind of position, so `[@@custard_extern]` on a binder or `[@@custard_inline_field]` on a declaration can never do anything and that is decidable now.  Warning 371 gains four shapes, including `[@@custard_c_header]` with no `custard_extern` beside it, and each says where the attribute does belong.  `check_decl_attrs` runs from the cached `binder_classes`, so once per definition rather than once per call site, and the two binder lists are merged positionally -- concatenating them reports the ordinary case twice.  `tests/custard/AttrPos.fst` |
| M10αμ | **A block argument's captures** (§34.3) | Done.  Round 41, offered by the reporter as a regression test.  Round 40's `[@@@monomorphize]`-on-a-`fn`-binder fix was measured on a real separation-logic loop combinator downstream, in a tree this suite does not build; `tests/custard/pulse/PulseForCapture.fst` reduces it to Pulse's own library.  A `fn` block captures a `ref` and a value from the caller's frame, neither a loop parameter, and the specialized loop takes both as parameters with the ghost apparatus gone -- and `main` checks its own answer, so a capture from the wrong frame is a nonzero exit rather than something to read out of the C.  Writing it found the non-obvious constraint Kuiper's `for_loop'` already satisfies: the invariant must be an explicit `slprop` parameter, because a body type that mentions a `ref` parameter carries §3.1 rule 5's demand onto that parameter and error 364 fires.  A ghost binder is what stops it, since rule 1 drops it before rule 5 can reach through |
| M10αν | **A public API whose types are generic** (§35.1) | Done.  Round 40's verification.  §32.9's open question -- a rename map for types -- is closed as *not built*, on the reporter's own evidence: they drove the real CBOR API from C++ off the generated header and three typedefs, two of which name types `--custard_c_no_prefix` already renames, and the rest of what a consumer wants are the `cbor_det_*` abbreviations, which are names *they* chose and Custard cannot know.  The finding is the third typedef, `CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__cbor_raw`, which has no source-level spelling at all: the type on the interface is a monomorphized instance, not a module's declaration, so `--custard_c_no_prefix` leaves it alone -- correctly, since §30.15's hints are depth-bounded, clipped and collision-suffixed and are exactly the names free to change.  What was missing is that nothing said so, and a consumer finds out by reading the header and writing the name down.  Decidable at print time -- a public prototype is in the header, a `TApp` in it with a `spec` is generated -- so `check_interface_names` reports warning 377, once per type and naming one definition that exposes it.  `tests/custard/ExportGen.fst` |
| M10αξ | **A property, not a warning** (§35.2) | Done.  Round 40's verification, and a correction to how M10αζ was checked.  That fix was confirmed by clang's `-Wparentheses-equality` going 78 to 0; the reporter showed the warning is *shape* sensitive -- `if ((a==b))` warns, `if ((g()==1))` is silent -- so a leftover pair around a call-comparison would have passed `-Werror`, which was the entire check.  They checked the property directly instead, over the real 198 KB `CBORDet.c`: 36 conditions beginning with `(`, zero a single redundant group.  `tests/custard/checkgroup.py` is that matcher generalized to every position and run on every C file all three suites emit, skipping comments, literals, and the parentheses that are C *syntax* rather than grouping -- `f((x))` is one grouped argument, not two pairs.  On output `-Wall -Wextra -Werror` had accepted it found three: a Pulse `while`'s exit test built its negation by hand rather than through `negate`, and `malloc` and the fill loop each wrapped a length `c_expr` had already parenthesized.  No compiler would have reported any of them -- `<` is not a comparison the warning looks at and a cast is not one either.  One `group` helper now, and `negate` defined in terms of it |
| M10αο | **A setting for no test** (§35.3) | Done.  Round 40's verification, found while wiring the above in.  `tests/custard/pulse/Makefile` had been accumulating `CGREP_`/`CNOGREP_` variables that no recipe read, so §34.3's assertions about the specialized loop's parameters and round 40's about `PulseMono` were set and never run.  M10φφ from the other side: there a test had settings and no registration, here settings had a registration and no consumer, and both read like coverage that does not exist.  The recipe applies them now, over the header as well as the source.  `check-settings` is the general form, in both directories and part of `all` -- every variable whose name is a known setting prefix must name a registered test -- four lines of `make` over `.VARIABLES`, and it reported four on its first run, all hand-written targets with their own `all:` line, now listed explicitly rather than made to look like list entries |
| M10απ | **A reference to a declaration that is not there** (§36.1) | Done.  Round 42, and the round's real finding: a rule may name a symbol that dead-code elimination has already deleted, and the output was written with no error and no warning.  Worse than not compiling, the name in it was the mangled `CustardRuleTest_kcall` rather than the `kpr_kcall` `[@@custard_extern]` gave it -- the declaration was never processed, so its target and header were never read, and the output looks like Custard ignored an attribute it never saw.  `check_resolved` is error 379, run immediately after `dce`, which is the pass that can remove what a reference needs, and before the passes that rewrite bodies so the name reported is the one the rule wrote.  Values and value references only; a missing type is already the backends' message.  Whole programs only: under `--custard_unit` a reference that leaves the unit is not in this program by design, and that exclusion is the whole-program assumption written down |
| M10αρ | **A rule's roots** (§36.2) | Done.  Round 42, the other half.  A launcher rule emits a call to a runtime entry point that nothing in the source calls, which is what makes it a launcher and also what makes it unreachable; `register_root` adds a `lident` to the roots next to `--custard_entry`'s, registered once beside `register_rule`.  Roots are collected before the extraction loop and a plugin is loaded before that, so there is no ordering to arrange, and an erased root is dropped exactly as `--custard_entry`'s is.  The rule test had been keeping `kcall` alive with a dead branch whose only purpose was to mention it; that is gone.  The reporter judged §36.1 the more valuable of the two before either was written, and they are right -- this stops one cause, that stops every reference to a name that is not there |
| M10ασ | **Lifting a named, decorated function** (§36.3) | Done.  Round 42.  `lift_lambdas` named what it lifted after the definition it came from, `CustardRuleTest_main__lam`; for a device backend that is the kernel's symbol and it appears in profiler timelines, in disassembly and in user-facing errors, and the descriptor already carries the name its author chose.  `lift_named : string -> list flag -> expr -> ML expr` makes a lambda a top-level declaration under that name used verbatim -- no namespace, no mangling -- and returns the `EQual`; a repeat is error 378, not a silent overwrite.  Closing the lambda stays the rule's job (§36.5).  The flags close round 33's gap 3: `Prologue`, `Epilogue`, `CInline` join `Comment`, all four reach karamel, and the C backend emits `Prologue` before the prototype as well as the definition, since CUDA wants `__global__` on both and a qualifier on one alone is a redeclaration error rather than a silently host-side kernel.  `Root` meant public, which is wrong for a lifted function, so `Private` overrides it |
| M10ατ | **A name is not a computation** (§36.4) | Done.  Round 42, a nit with a one-line cause.  A rule building `EApp (EQual kcall, args)` labels the node that *names* the function with the function's effect, which is the effect the application has, and `anf_expr` hoists every operand that is not pure -- so the call went through a temporary function pointer while a source-level call to the same function was direct.  `EQual`, `EVar`, `EConst` and `EAny` denote without evaluating and there is nothing for a binding to sequence, whatever the node's effect says.  Cosmetic for a C compiler, not cosmetic for generated device code a human reads |
| M10αυ | **`Rule_prim` reproduces `hoist`** (§36) | Closed, no change.  Round 42 answered §34's open question by measurement rather than argument: the reporter gave the rule test's descriptor a `kbody` written at the launch site over a local, saw it arrive as an `EFun` open in that local -- exactly `hoist`'s input -- closed it over its free variables and let §19.12's `lift_lambdas` push it out.  `Rule_prim_st` is not needed and is not being added.  Their clang measurement is the round's other closed item: clang 14 on the whole `tests/custard` suite is exit 0 with no warnings, and all 25 `_output/*.dc` files rebuilt under `-Weverything` minus style checks produced a diagnostic in 0 of 25 -- which is the coverage this tree cannot produce, since clang is not installed here |
| M10αφ | **A cast ends in a closing parenthesis too** (§37.1) | Done.  Round 41 of the EverParse trial, and the reporter checked M10αξ's checker the way M10αξ says to check things -- by building the case it should catch rather than watching it pass.  `is_syntactic` skipped a `(` preceded by `)`, which is right for a call through an expression, but a *cast* ends in `)` as well and what follows a cast is its operand, where a parenthesis is grouping: `(int)((5))` was silent while `((5))` was reported.  Not hypothetical -- it is the shape of the third of the three findings M10αξ was written after, the fill loop's `(size_t)(((size_t)1ULL))`, so the gate would not have caught a recurrence of one of the bugs it exists to prevent.  The matcher now looks inside the preceding group and calls it a cast when the content is type-ish.  Calibrated: zero live instances of the shape in ~600 KB of real output, and the two matchers agree everywhere there, so this was a hole in the gate and not a bug in the output.  `--self-test` carries the three real findings and the distinguishing pair, and runs with the suite |
| M10αχ | **What round 41 confirmed** (§37.2) | Closed, no change.  M10αζ's three parenthesis fixes were live bugs downstream and not just in this suite -- the `if (!((...)))` shape was in every CDDL unit, six per unit and eight in `signoutputargs`, for two rounds, with no compiler saying anything, since `!` and `&&` are not the `==` `-Wparentheses-equality` looks at.  Warning 377 fires twice on the CBOR unit and names exactly the two shim typedefs of round 40's four that had no source-level spelling, and on the CDDL units names the slice and option the behavioural driver has hardcoded since round 36 -- the count and the identities both match, so it found the real consumer without being told.  M10αο's guards were broken rather than observed, both failing as intended.  And the first full CDDL behavioural re-run since round 36, because the parenthesis fix touched loop exit tests: 12,110 vectors per entry point, three entry points, all identical to golden, CBOR-to-Rust byte-identical, COSE interop intact |
| M10αψ | **Floating point** (§38) | Done.  Round 33's gap 1, the largest of Kuiper's asks and the one whose answer was least in doubt: a float add went through a `custard_extern` and stayed an opaque call where `u32` got `+`.  `FStar.Float32` and `FStar.Float64` are shaped exactly like the machine-integer modules, so the rules are too, and follow `FStarC.Extraction.Krml`'s naming for the same reason the integer ones do.  `TFloat of fwidth`, `CFloat of string & fwidth`, and `ECast` for `of_int`, which rounds above 2^53 and is therefore not a coercion.  `bit_eq` stays a call, as it does in karamel: it distinguishes the two zeros and makes a NaN equal to itself, which no comparison operator does.  C gets `float`/`double` and its own operators, karamel gets the widths it already had, OCaml gets its own `float` and `+.`  `tests/custard/Floats.fst` checks its own answers and exits nonzero on any that is wrong; `tests/custard/FloatsKrml.fst` does the same through karamel and `tests/custard/FloatsML.fst` through OCaml |
| M10αω | **A width that is not an integer width** (§38.2) | Done, with §38.  `prim_op`'s `po_int : option (signedness & width)` became `po_ty : option prim_ty`, because most of its readers ask only \"is there a width here\" and a few mean *integer*: `And`, `Or` and `Not` are bitwise at a width and connectives without one, and a modular operation at `uint8_t` or `uint16_t` needs truncating because C promotes to `int` before operating.  Those sites say so through `at_int_width` now.  A breaking change to the plugin surface, and deliberately a rename rather than a second optional field -- a rule that builds a `prim_op` has to be edited either way, and a record with two optional fields of which at most one may be set is an invitation |
| M10βα | **A float literal is text** (§38.3) | Done, with §38.  `of_literal`'s string is emitted as written, because parsing it to a float here and printing the float again rounds twice and the second rounding is not the author's.  Emitting text means checking it, against the conservative grammar `FStarC.Extraction.Krml.valid_float_literal` uses, and error 380 is the difference between a diagnostic and `1.0); abort(); (` in somebody's C -- which is `tests/custard/FloatLit.fst`.  In C the text carries its width's suffix, since an unsuffixed literal is a `double` and `1.5f + 2.25f` written without one would be computed at double precision and rounded once at the end.  On OCaml `Float32` is refused with 368 rather than computed at binary64: a backend that cannot round right should say so |
| M10ββ | **A karamel bug, found on the way** (§38.6) | Open, upstream.  karamel's constant folder reads the operands of a `Mult`, `Div` or `Mod` at `TInt w` with `Z.of_string` before checking that `w` is an *integer* width -- `Add` has that guard and the other three do not -- so `F64.div (F64.of_literal \"1.0\") (F64.of_literal \"4.0\")` ends the run with `Invalid_argument(\"Z.of_substring_base: invalid digit\")`.  The neighbouring rewrites are wrong rather than loud: `0 * x -> 0` and `0 + x -> x` hold at no float width, since `0.0 * nan` is `nan` and `0.0 + (-0.0)` is `0.0`, and `of_literal \"0\"` satisfies §38.3's grammar so both are reachable.  The fix is the guard `Add` already has; until then `tests/custard/FloatsKrml.fst` computes with variables where `tests/custard/Floats.fst` computes with literals, which is the whole reason there are two.  Custard's own C backend folds nothing |
| M10βγ | **Literals are values, not text** (§39) | Done, user report.  `CInt of string & option (signedness & width)` carried the source spelling through the whole pipeline, which is the shape the ML extraction has and the shape karamel has, and which the F\* compiler itself abandoned -- `Const_int` is `int & int_base`.  `CInt of int & int_base & option (signedness & width)` now, with the base kept because someone wrote `0xff` and should not be shown `255`, and `const_eq` ignoring it because it is not part of the number.  Nobody reported a bug, and there were three: `PrintC.is_one`, which decides whether a `BufCreate` can be a plain local rather than an allocation, tested `CInt (\"1\", _)` and gave a one written `0x1` an allocation; `int_literal`'s `INT64_MIN` case, which exists because C has no negative literals, compared against 20 decimal characters and wrote an undiagnosable literal for any other spelling; and every construction site rendered a number to build one, including a `BU.int_of_string` in the rule plugin reading back what `show` had just written |
| M10βδ | **A float is a real and a sign** (§39.2) | Done, with §39.  `CFloat of float_lit & fwidth`, where `float_lit` is a `bool` and an `FStarC.Real.real` -- the exact rational, canonical, so two literals are equal exactly when they denote the same number.  The sign is separate because IEEE 754 is sign-and-magnitude and a canonical rational is not: `-0.0` and `0.0` are the same real and different floats, `bit_eq` tells them apart, `1.0 / -0.0` is negative infinity, and `Real.mk 0 e` is `0` whichever sign it was given.  Nothing else was lost -- `real` is exact and unbounded, so rounding is still the target compiler's job done once, and `1.5e-3`, `0.0015` and `+15e-4` are one literal.  `float_lit_of_string` replaces `valid_float_literal`: a predicate that text is well-formed and a function that turns text into a value are the same walk, and having only the second means a literal cannot be accepted without knowing what it is.  `tests/custard/LitBase.fst` |
| M10βε | **Half and bfloat16 without a compiler change** (§40) | Done, user question, and the answer is that the facility is already there.  §38.5 left `Float16` out because the missing half is a `ulib` module to extract from and a C spelling to extract to, both facts about a target; that is an argument for not guessing in the compiler and not an argument for waiting.  `tests/custard/Half.fst` declares `__half` and `__nv_bfloat16` with §14.5's `[@@custard_extern]` and gets exactly what nvcc wants: no typedef emitted, the header included, `__hadd`/`__hmul`/`__hlt` by name -- which is the *faithful* translation and not a workaround, since CUDA's half arithmetic is functions in C and the operator overloads are C++.  And they are ordinary F\* types, so `twice hadd` monomorphizes to `Half_twice__half` and a record of one of each lays out as a struct.  What it does not get is a literal or an `EOp`, which is what a `TFloat Float16` would still be for |
| M10βζ | **The blit's hand-written parentheses** (§41.1) | Done.  Round 42, EverParse, and a live printer bug: §35.2 routed every parenthesized operand through `group` and missed the `BufBlit` length, which kept the hand-written `"(" ^ lenv ^ ")"` that `group` exists to replace -- the last one in the file, the two neighbouring length positions in the same case having been converted.  Unreached rather than unnoticed: `Pulse.Lib.ArrayPtr.memcpy` is the only rule that produces a `BufBlit` and no test called it, so §32.10's gate had nothing to look at.  `tests/custard/pulse/PulseBlit.fst` calls it and the gate reported the bug on the first run, which is the second time it has found something the sweep that installed it did not.  Latent for the reporter: their one real `memmove` passes a struct field, which is not already a group, so every output is byte-identical with the fix in |
| M10βη | **A self-test that tested the wrong bug** (§41.2) | Done.  Round 42, and the round's better finding: §37's `--self-test` was mutation-tested, fourteen branches, six survivors, and the one that matters is emptying `CHECKED_KEYWORDS` -- after which the gate is blind to `if ((cond))`, `while ((cond))` and `return ((x))`, which is §32.10's bug, the one the matcher was written for, and the self-test still passes.  Structural rather than an oversight: every positive case was a round-41 finding and round 41 was about casts, so all five had the redundant group behind `!`, `=`, `(` or a cast and nothing ever read the keyword table on a path that decided an outcome.  Six new cases close four of the six gaps; the other two mutants are equivalent, checked over 659 KB of real output rather than assumed |
| M10βθ | **The keyword set is complete with respect to the printer** (§41.3) | Closed, no change.  Round 41's three unchecked shapes -- `sizeof((5))`, `case ((1)):`, `else ((p));` -- cannot be produced: `sizeof(` is emitted at two sites and always around a *type*, where the parentheses are mandatory; `else` at three, always before `if (` or a brace; `switch` and `case` not at all.  Recorded because the form of the argument is the point.  A gate on generated code should be justified by what the generator can write, not by what a corpus happens to contain, and the second is what grepping the output would have given |
| M10βι | **What nvcc said** (§41.4) | Closed, no change.  §36 was designed without an `nvcc` and three of its answers are now checked against one.  `Prologue` on the prototype as well as the definition was load-bearing rather than defensive: `nvcc` rejects a `__host__` function redeclared with `__global__`, so the flag on the definition alone would have made *every* generated kernel fail to compile.  The output is a kernel and not C that resembles one -- `nvcc -ptx` gives `.entry`, `cuobjdump -symbols` gives `STO_ENTRY`, and `-Xcompiler "-Wall,-Wextra,-Werror"` is clean.  And `lift_named`'s guarantee is about the C source, which `nvcc` compiles as C++: `kernel` is `_Z6kernelj` in the object file, which profilers demangle and a lookup by string does not, and a program doing the latter wants an `extern "C"` that is a `Prologue` away.  The name is the point: the same kernel through the existing plugin is `__hoisted_reduce_u32_0` |
| M10βκ | **Gap 1, checked** (§41.5) | Closed, no change, and a correction.  Reported five times as "float widths dropped from `KrmlAst.width`", most recently as what stops an existing karamel plugin building against upstream.  `FStarC.Extraction.KrmlAst.width` has `Float32 | Float64`; so does karamel's `Constant.width`; so does its `InputConstant.width`, which is the one that matters, being the wire type of the `.krml` file, marshalled positionally, and carrying the `Bool` width the internal type lacks for exactly that reason with a comment saying so.  §38's krml backend went end to end through all of it before this was checked, which is the evidence.  What is genuinely absent everywhere is `Float16` and `BFloat16` -- §40 is what a program needing them can do today, §38.5 is what adding them would take |
| M10βλ | **A C unit offers its linking interface** (§42.1) | Done.  The decision that made the rest of §42 fall out, and the one that had to be made first: a `.cui` for the C backend exports what the header declares, so `Driver.unit_entries` drops a `DLet` that `PrintC.is_public` refuses.  Asymmetric with OCaml, which exports every declaration a request created, and necessarily so -- `static` is what makes two whole-program C files linkable at all, and a `static` definition offered in an interface is a symbol the consumer cannot name.  It also stands §12.7's per-unit symbol prefix down: statics cannot clash whatever they are called, and what is left with external linkage is what `--custard_entry` asked for |
| M10βμ | **Headers include headers** (§42.2) | Done.  An imported declaration is skipped at every emission site and still handed to the printer, so the type, constructor, arity, unit-parameter and rename tables see it -- the same split §12.4 rule 2 makes in the middle of the pipeline.  The header file to include is recorded in the `.cui`, since `-o` names it.  Exporting every `DType` is what keeps two headers from defining one `struct` twice; the alternative of an `#ifndef` guard per generated type would have been unsound, because §12.3 says names are not deterministic and two units may give one name to two types.  `custard_unit` does get a guard, for the reason the generated types could not have one: it is a fixed name for a fixed type, so two spellings of it are the same spelling |
| M10βν | **A namespaced global initializer** (§42.3) | Done.  `custard_init_globals` is one fixed name per unit and two in a link is a duplicate symbol, so under `--custard_unit U` it is `U_init_globals`; the unqualified spelling is kept with no unit name, leaving every existing whole-program output unchanged.  Renaming it raised the question whole-program mode never had: `main` calls each linked unit's initializer in `--custard_link` order before its own, and since that order is the user's and need not be topological, the body gets a `static bool` re-entry guard -- under `--custard_unit` only, since in whole-program mode there is exactly one caller and the branch would be noise |
| M10βξ | **`uh_header`, `uh_init`, and a version bump** (§42.4) | Done.  A `.cui` is loaded positionally by `Util.load_value_from_file`, so growing the header is deliberately not a compatible change; the version check is there so that a stale interface is an error rather than a miscompilation |
| M10βο | **A two-unit C test** (§42.5) | Done.  `tests/custard/SepLibC.fst` and `SepAppC.fst`, compiled separately, linked, and run.  `nm` checks the three things a C compiler cannot: the exported root has external linkage under its own name, the private helper is in neither object's symbol table, and the library's definitions are in exactly one of the two -- which is the only direct evidence that the downstream unit reused rather than recompiled |
| M10βπ | **C octal and binary literals** (§43.1) | Done.  Round 43.  `Syntax.c_int_lit_to_string`, used only by `PrintC.int_literal`: F*'s `0o17` becomes C's `017`, and `0b1010` becomes `10` because C has no binary literal before C23.  The C backend had been emitting `0o17U`, which no C compiler accepts.  `LitBase` covered only hex and decimal -- the two bases whose F* and C spellings coincide -- so it was testing the agreement rather than the translation |
| M10βρ | **The base on the karamel path** (§43.2) | Done.  Round 43.  `PrintKrml.krml_int_lit` at all four integer-spelling sites, replacing the unconditional `show v` §39.1 had recorded as deliberate.  Rust gets every base; **KrmlC gets hexadecimal or decimal and never octal**, because karamel parses the constant text back as decimal somewhere on the way to C and `017` returns as seventeen -- silently, and with a spelling a `CGREP` would have accepted.  Hex survives the same trip, which is what makes it easy to miss |
| M10βσ | **The binary32 literal suffix** (§43.3) | Done.  Round 43.  `PrintKrml.krml_float_lit` writes `f` into the constant text at `Float32` on the KrmlC path.  karamel's suffix table (`karamel/lib/PrintC.ml:245`) has no float case, so the constant went out bare -- a `double` -- and the `(float)` karamel inserts fixed the type and not the value: decimal to binary64 to binary32 is a double rounding, and `7.038531e-26` lands on `0x15ae43fe` instead of `0x15ae43fd`.  A workaround for an upstream one-liner; if that lands this must go the same day or the output reads `1.5ff` |
| M10βτ | **`LitOct` and `LitF32`** (§43.2, §43.3) | Done.  Round 43.  Both run on the direct C backend *and* through karamel, and both check their own arithmetic rather than their own spelling: `main` compares each value against its decimal and returns which one was wrong.  That is the only assertion that can see the karamel octal bug, whose output greps clean.  `LitF32` was confirmed to fail when the suffix is stripped from the generated C by hand |
| M10βυ | **Gap 1 withdrawn; §40 validated on real CUDA** (§43.4) | Done.  Round 43.  The reported missing `Float32`/`Float64` was a missing `Float16`, which §41.5 had already said does not exist anywhere; Kuiper withdrew the request.  §40 was then compiled, linked and run against the real `<cuda_fp16.h>`/`<cuda_bf16.h>` under `nvcc`.  Two notes recorded: two F* `val`s may share one `custard_extern` target, because CUDA overloads `__hadd` rather than offering `__hadd_bf`, and monomorphization plus C++ overload resolution handle that unaided -- `Half.fst` keeps the invented `__hadd_bf` only because its stub is compiled as C11, where there is no overloading and where a `_Generic` macro cannot be the function pointer `twice` wants; and `EOp (Lt, Float16)` is a latent consumer bug, since `operator<` on `__half` is C++-only and `#if`-guarded while `__hlt` is not |
| M10βφ | **A constant pattern karamel cannot hold** (§44.1) | Done.  Round 44.  `krml_pat`'s `PConst _` fell through to a fresh *variable* pattern, which matches everything, so the first string, float or character pattern swallowed the scrutinee and every branch after it was dead -- a three-way `classify` became the constant `1`, with no diagnostic on either krml backend.  The only trace was karamel's own `KRML_MAYBE_UNUSED_VAR`, which nothing greps for.  `LitOct` goes through karamel clean because its `match` is on integer patterns, the one kind that works |
| M10βχ | **`krml_reject`** (§44.1) | Done.  Round 44.  The three refusals in `PrintKrml` were `failwith`s that said "not supported by **the C backend**" -- from the file that is not the C backend, sending a reader to a printer where nothing refuses it.  Now an `Error_CustardNoCRepresentation` that names karamel, says its AST has no node for the construct, and says that `--custard_backend C` may accept it, which for all three it does.  §33.4's rule about wrong explanations covers wrong addresses too |
| M10βψ | **String equality is `strcmp`** (§44.2) | Done.  Round 44.  `Prims.string` is `const char *`, and both `pat_tests`'s `PConst` case and the `Eq`/`Neq` infix case emitted `==` on one -- a comparison of addresses, which gcc diagnoses as `-Waddress`.  `is_string_ty` plus `strcmp` at both sites, using the `<string.h>` every generated header already includes.  Zero live instances: EverParse's output has no `Prims_string` in it, and no test matched on a string, which is why all three sites survived |
| M10βω | **`PatStr` and `PatStrKrml`** (§44.1, §44.2) | Done.  Round 44.  The C test gets its strings from a `custard_extern` that `malloc`s a copy, because **the buggy program exits 0 when every string is a literal**: the C compiler pools literals, so comparing them by address agrees by accident, and a test written the obvious way tests the pool.  Confirmed to fail when the `strcmp`s are edited back to `==` by hand.  `PatStrKrml` pins the 368, and pins that the message no longer names the wrong backend |
| M10γα | **Five Kuiper units under `nvcc`** (§44.3) | Done, round 44, no change required.  Five real kernels extracted as five C units, each compiled under `nvcc` as C++ and `clang -Wall -Wextra -Werror` as C, linked and run; no duplicate global symbol, and all five headers coexist in one TU.  It also sharpens §42.1 from tidiness to soundness: two units hold `Kuiper_Array_Core_slice_read__t` at `u64` and at `u32`, the same generated name at incompatible types, harmless only because both are `static` -- had the `.cui` exported everything a request created, that would have been the common case across 62 units, not a corner one |
| M10γβ | **A `custard_extern` target is used verbatim** (§45.1) | Done.  Round 45.  `PrintC` printed a value target through `escape_kw (sanitize t)`, which turns `wmma::mma_sync` into `wmma__mma_sync` -- sanitizing does not make an illegal identifier legal, it makes an existing symbol absent.  The external *type* path had been verbatim since §14.5, which is why a program could get `auto&` in type position and a mangled call on the next line.  2,530 `wmma::`-qualified references across 9 names in Kuiper's shipped output, all on the callee side |
| M10γγ | **A target that cannot be declared** (§45.1) | Done.  Round 45.  Verbatim raises what sanitizing hid: Custard emits a prototype for an external with no `[@@custard_c_header]`, and `extern void wmma::mma_sync(...)` is not a declarator.  Now refused, with a message saying which of the two to add.  The old spelling turned this into a link error a long way from its cause |
| M10γδ | **Source-level C decorations** (§45.2) | Done.  Round 45.  `Prologue`, `Epilogue`, `Comment` and `CInline` existed as flags, both printers honoured them, and `Extract` never constructed one -- the only route was `B.lift_named` from a rule plugin, which for 654 `__global__` kernels means a rule per kernel to say a thing F\* has had an attribute for since karamel did.  `c_decoration_flags` reads them off the definition, from the sigelt's attributes *and* the letbinding's, deduplicated: F\* records them in both places, which one they land on is not stable, and two `__global__`s is a syntax error rather than a redeclaration |
| M10γε | **An external karamel declared and never called** (§45.3) | Done.  Round 45.  `PrintKrml` emitted the `DExternal` under the `custard_extern` target and every call site under the F\* name, so the TU declared one symbol and called another and neither half was ill-formed on its own.  `extern_values`/`value_lident_of_name`, the counterpart of the `extern_types` table the type path already had.  The `custard_c_header` include was missing too, so even the right name would have been undeclared; it now rides on the `DExternal` as a karamel `Prologue`.  Second round running in which the three backends disagree about one construct, the same way round: C is where the attention has been |
| M10γζ | **`TensorC` and `KrmlExt`** (§45.1-§45.3) | Done.  Round 45.  `TensorC.fst` is the TensorCore shape reduced to what a C11 compiler can host: a type whose C spelling is not an identifier, calls whose names are not identifiers, and the three decorations a CUDA kernel is made of, pinned as appearing on the definition and the prototype and **exactly once on each**.  `KrmlExt` asserts by *linking*, which is the only assertion that sees a declaration and a call that name different symbols |
| M10γη | **Indexed `TExtern` withdrawn** (§45.4) | Withdrawn by the requester, round 45, and worth recording as a method note rather than a feature.  Kuiper never emits `wmma::fragment<...>`: its plugin declines to, because the indices are erased before it sees them, and the shipped `dist/` never names the type at all -- it is `auto&`, inferred from a macro call.  The request had been made from reading the plugin's intent rather than its output.  With §45.1 and §45.2 in, the TensorCore kernel is expressible with today's IR, and was compiled under `nvcc -arch=sm_70` to a real `wmma.mma.sync.aligned.row.row.m16n16k16.f16.f16`.  Still unknown: whether the per-configuration macro names can be *generated* from the erased indices, which §34.1's reduced arguments may make possible |
| M10γθ | **A character constant is a `uint32_t`** (§46.1) | Done.  Round 46.  `krml_const`'s `CChar` was an `EAbortS`, which is a translation and not a refusal: the program extracted with no diagnostic, compiled, linked, and aborted at run time -- on the Rust path, a `panic!` in a Rust binary quoting a message about the C backend.  The message also named the wrong component, and its claim was false in the other direction: the direct C backend has emitted `((uint32_t)97)` since §6.  `prim_type` now carries the representation krmllib and `PrintC` had both always agreed on, and a character *pattern* follows from it |
| M10γι | **An opaque `FStar_Char_char`** (§46.2) | Done.  Round 46.  `FStar.Char` is realized, so its `char` reached `krml_typ` as an opaque `TQualified` and got `typedef struct FStar_Char_char_s FStar_Char_char;` against krmllib's `typedef uint32_t FStar_Char_char;` -- a header that would not compile, from a program with **no character constant in it**, extracted at rc=0 with no diagnostic.  Fixed by the same line as §46.1, because `krml_decl` already drops a `DType` that has a `prim_type`.  The `KrmlRust`-only `is_krml_model` gate had looked like the mechanism and was not |
| M10γκ | **`ETry` discarded its own body** (§46.3) | Done.  Round 46.  `ERaise` and `ETry` shared one `EAbortS`.  For `ERaise` that is defensible; for `ETry` it deletes the protected expression, so a `try` whose body never raises returned no answer rather than the wrong one, and karamel said only "the exception was dropped", at warning level, exit 0.  `ETry` is refused as `PrintC` already refused it; `ERaise` may stay an abort *because* `ETry` is refused, which is also what keeps `TExn -> TAny` honest |
| M10γλ | **`krml_reject` says where to go** (§46.3) | Done.  Round 46.  §44.1's shared second line hedged that the direct C backend *may* accept the construct, and the hedge was wrong at four of six sites -- only a string and a float pattern survive the crossing.  Split into `krml_reject_c_ok` and `krml_reject`; `TryOk` pins the absence of the wrong sentence |
| M10γμ | **`make check-sources`** (§46.4) | Done.  Round 46.  A `NOEGREP` pins a phrase as absent from one test's output; round 44's passed while two other sites in the same file still emitted the phrase, one of them into a Rust binary.  Whether the *compiler* can still emit a sentence is a question about the sources, and a grep answers it in a second.  Runs as part of `all`.  The general point is that a test pins what a program produced, and some properties are about what the compiler contains |
| M10γν | **`ChrLit`, `ChrTy` and `TryOk`** (§46.1-§46.3) | Done.  Round 46.  All three check their own answer rather than grepping for a spelling (§43.2).  `ChrLit`'s match is deliberately out of source order, so a character pattern that fell back to a variable pattern would return 1 instead of 0.  `ChrTy` takes its char from a `custard_extern` so that it contains no literal, which is what makes it a test of §46.2 rather than of §46.1.  `TryOk` is a reject test on the krml backend; its negative control put the old `EAbortS` back and confirmed that `attempt()` compiles to a bare abort with the call to `safe` gone |
| M10γξ | **A tag enum C++ cannot see** (§47.1) | Done.  Round 47.  Enumerators of an enum nested in a struct have file scope in C and *class* scope in C++, so every tagged union Custard emitted compiled clean as C11 and was unusable from nvcc -- seven of the suite's units, with `clang -Weverything` reporting nothing, correctly, because as C the code is right.  The enum is now declared beside the struct, which is still C11 and changes neither meaning nor layout.  `extern "C"` does not help and it is worth knowing why: linkage is not scope |
| M10γο | **A C++ leg in the test suite** (§47.1) | Done.  Round 47.  Every generated unit is compiled a second time as C++17 with `-fsyntax-only`, `-Wall -Werror`.  Custard does not target C++; a generated header is meant to be *included* by a consumer, and CUDA is a consumer.  A second front end is the only thing in the suite that could have found §47.1, because everything the C leg checks was already right.  All 34 units pass, which is the other half of the finding: one construct, not a class of them |
| M10γπ | **An indexed external type** (§47.2) | Done.  Round 47.  §30.11 rule 4 froze a type mentioned in an external's signature, because a clone would name a declaration the realization does not define -- right in general, vacuous when the type carries its own C name, since an external's spelling is a fixed string with nowhere for an argument to go.  `mono_cty` now drops an external type's arguments; no clone is requested, so nothing needs freezing.  The unindexed-external-plus-abbreviation workaround still works and is no longer forced |
| M10γρ | **§45.4's open question, answered** (§47.2) | Resolved, round 47, with no code.  Whether a rule could *generate* per-configuration C names from erased indices turned out to be the wrong question: F\* already has the mechanism, in a typeclass whose indices are erased and whose instances name the targets.  A body polymorphic in the configuration extracts to the same C as a hand-written one, and the dispatch disappears.  Two prerequisites, both consequences of existing rules: erase every index the C side does not take (a concrete enum index goes out as a spurious leading argument, *silently*), and put `inline_for_extraction noextract` on the class, not only the instances |
| M10γσ | **`FragCfg`** (§47.2) | Done.  Round 47.  The TensorCore fragment API at C11 scale: an indexed `custard_extern` type, three externals selected by a typeclass whose indices are all erased, and a body that never names a configuration.  Checks its own answer rather than a spelling, and pins the absence of any emitted declaration for the external type |
| M10γτ | **A C++ target is direct-C only** (§47.3) | Recorded, round 47, not fixed and not a Custard bug.  §45.3 made a C++-qualified program nearly work through karamel; karamel then sanitizes names of its own downstream of Custard (`wmma::fill_fragment` to `wmma__fill_fragment`, `auto&` to `auto_` -- §45.1 again, in the other repository) and emits a prototype for an external that already has a declaring header, which `PrintC` suppresses and karamel has no rule for.  Documented so nobody spends an afternoon on the krml route |
| M10γυ | **A fallback that claimed too much** (§48.1) | Done.  Round 48.  `krml_pat`'s unclassified-constant case routed through `krml_reject_c_ok`, which tells the reader the direct C backend accepts the construct -- true of two of the six things `krml_reject*` is called for, and §46.4 had just split the function for exactly that reason.  Unreachable since §46.1 gave `CChar` a case, so it was dead *and* wrong, and would have started lying on the day a seventh constant constructor was added.  Now `CString` and `CFloat` are named (`c_ok`, correctly) and `_` takes the strict refusal.  The rule: a fallback carries the weakest claim, not the claim that was true of the cases it was written for |
| M10γφ | **Float patterns are unreachable from source** (§48.1) | Resolved, round 48, with no code.  Carried as an uncertainty for three rounds and answerable in one command: F\* rejects a float literal in pattern position at *parse* time, Error 168 "This is not a valid numeric literal", for both `1.0` and `1.0f`.  The `CFloat` case is kept because the IR can hold one, with a comment saying the parser will not build one |
| M10γχ | **`check-sources` reaches the interfaces** (§48.2) | Done.  Round 48.  `CUSTARD_SRC` was `*.fst`, 18 files, and missed the 18 `.fsti` beside them.  Latent rather than live -- no interface carries diagnostic text today -- but a check whose reach is smaller than its subject passes for the wrong reason exactly once.  Negative control put the phrase into an `.fsti` and confirmed it fires |
| M10γψ | **A string match on the krml backend** (§48.3) | Done.  Round 48.  §44.1 refused string patterns because karamel's `pattern` cannot hold a string constant; correct about the AST, but not forced, because karamel handles string *equality* fine -- `krmllib/c/prims.c:24` realizes `__eq__Prims_string` as `strcmp(s1, s2) == 0`, which is the same comparison `pat_tests` builds by hand for direct C.  `PrintKrml` now desugars a flat string match into that if-chain, binding the scrutinee once.  The guard is narrow on purpose: a string constant nested in another pattern, or a `when` clause, still falls through and is still refused |
| M10γω | **Polymorphic equality needs its type application** (§48.3) | Done.  Round 48, and the reason the above failed first.  Emitted as a bare `EApp (EOp (Eq, Bool), args)`, karamel's checker reads the operator's *width* as the operand type, decides the arguments should be booleans, and drops both definitions with `subtype mismatch: Prims_string vs: bool`; the first symptom is a C compiler complaining about an implicit declaration, because with `-silent` karamel drops the definition without a word.  Decidable equality is typed only through `ETypApp (EOp (Eq, _), [t])` (`Checker.ml:592`).  Custard already knew this -- the null-pointer comparison and the general `EOp` case both do it, a few lines above.  The new code had to do what the code beside it was doing |
| M10γϊ | **`PatStrKrml` runs, `PatStrNest` refuses** (§48.3) | Done.  Round 48.  `PatStrKrml` was a reject test for two rounds and now checks its own answers; it takes its strings from a malloc-ing external for the same reason `PatStr` does (§44.2), and supplies `__eq__Prims_string` from its stub header because the suite links krmllib's *minimal* distribution -- a krmllib dependency, not a Custard one, and one any program comparing two strings through krml already has.  `PatStrNest` is the negative control: `Some "a"` is not a flat string match, so it still reaches `krml_pat` and is still refused, with a `NOEGREP` pinning that the message does not mention the if-chain |
| M10γϋ | **Source comments cited the wrong section** (§48.4) | Fixed, round 48.  Round 47's commit copied the reviewer's round numbers into six source comments and three test files as `Section 48.1`/`Section 48.2`; this document is one lower and has been since §46, so the comments pointed at a section that did not exist.  The divergence had been stated in a PR reply and needed stating in the sources, where a reader of a comment actually is.  A round report's headings get renumbered on the way in, not copied |
| M10γΐ | **Three negative results, recorded** (§48.5) | Recorded, round 48, no code.  `builtin_type` is a subset of `prim_type` after §46.1, with one *correct* divergence -- `Prims.int` is deliberately absent from `builtin_type`, since unbounded arithmetic has no C11 representation while karamel has `krml_checked_int_t`.  `krml_op` is total and 1:1 over 22 operators, and the `\| _ -> K.CInt` width fallback beside it is reachable only for `Prims.int`.  Every `==` site in `PrintC` audited: two enum tags, two `NULL`, two the string pair.  Plus the one the reviewer found on himself, which is the one worth keeping: string `==` was fixed in direct C in round 44 and the krml backend was never asked the same question.  It was right -- but "fixed in one backend, never checked in the other" is §44 and §46.1 and §48.3, and the cheapest place to catch it is the first fix |
