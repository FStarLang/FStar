master
==========

Guidelines for the changelog:
- There should be an entry, however brief, for each user-facing change to F*.
- Entries should include a link to a PR if at all possible, which can provide
  rationale and a detailed technical explanation.
- Each section lists PRs in ascending numerical order, then entries without a PR
  in roughly chronological order.
- Changes that break existing code should explain how to update the code,
  possibly with details in the PR or links to sample fixes (for example, changes
  to F*'s test suite).

# Version 0.9.7.0

## Tactics & Reflection
  * PR https://github.com/FStarLang/FStar/pull/2785 changes the reflection syntax
    for computation types, by removing universe field from the Total and GTotal
    comps. It also moves the decreases clause to the general C_Eff case.

    This is a breaking change for the reflection clients, but the regressions should
    only be syntactic.

  * As a better fix for Bug2635, F* now has a memoizing core typechecker for total
    (including ghost terms that are total) terms. The unification solutions, including
    those computed in the tactics engine, are typechecked using this core typechecker.

    This is a breaking change, since the core typechecker may fail to typecheck those
    solutions, or produce SMT guards that, for example, may need to be handled by the
    tactics.

    There are a couple of ways to maintain backward compatibility.

    There is a new command line option (also settable via `#set-options` in a file)
    `--compat_pre_core <n>` , where n is either 0, 1, or 2. Value 0 is most permissive and
    value 2 is most strict, with the metric being how much of the core typechecker is applied.

    This flag is a global setting that applies "relaxed" treatment to all the unification
    solutions. For controlling this more locally, there is a new tactic primitive
    `with_compat_pre_core` (see https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Tactics.Builtins.fsti),
    that applies the compat pre core setting only to the input tactic invocation.
    See https://github.com/FStarLang/FStar/blob/master/ulib/experimental/Steel.Effect.Common.fsti
    for an example usage.

  * Pat_Dot_Term now only has an `option term` as argument, where a `Some e` indicates that
    the dot pattern has been resolved to `e`.

  * Pat_Cons, the case of constructed patterns, now takes an additional argument representing
    the universe instantiation of the constructor.
  
  * The behavior of `pack` was changed to canonize arrows by flattening them in the internal
    compiler representation (https://github.com/FStarLang/FStar/pull/2609).
    An alternative version of `pack` called `pack_curried` which does not perform canonization,
    thus retrieving the previous behavior was also exposed.

  * Mutually recursive let bindings are now supported in the reflected syntax, using the
    same constructor (`Tv_Let`) as before (https://github.com/FStarLang/FStar/pull/2291.
    Inspection of a let binding now usually looks like this:
    ```
    match inspect_sigelt se with
    | Sg_Let r lbs ->
      let lbv = lookup_lb_view lbs (inspect_fv fv) in
      lbv.lb_def
    ```
    Where `lookup_lb_view` looks for a `name` in a list of let bindings, returning the corresponding let binding view. In turn, packing a let binding usually takes the form:
    ```
     let lbv = {lb_fv=fv;lb_us=us;lb_typ=ty;lb_def=def} in
     let lb = pack_lb lbv in
     let se = pack_sigelt (Sg_Let false [lb]) in
     ...
    ```

  * Bug2635, reported by Benjamin Bonneau, revealed an unsoundness in
    the way the tactic engine was using the unifier. In some cases, it
    would enable terms at a weaker type to be accepted as solutions
    for a goal at a refinement type, without presenting any goals for
    the refinement formula itself. This is now fixed by adding a phase
    at the end of tactic evaluation that checks that any
    as-yet-unchecked solution actually has the type of the goal. If
    this check fails, F* reports Error 217 and suggests to use the new
    primitive tactic
    `gather_or_solve_explicit_guards_for_resolved_goals` which
    collects all those refinement goals and presents them to the user
    tactic for furhter processing.

  * A new version of the tactics and reflection engine was started by
    PR https://github.com/FStarLang/FStar/pull/2960. The new version is
    under the `FStar.Tactics.V2` and `FStar.Reflection.V2` namespaces
    and should be considered *experimental* and subject to change. The
    old version is still supported, available under the corresponding V1
    namespaces. All the old, unqualified modules point to V1, so users
    should not need to make any change to their code to continue using
    V1.

## Typeclass argument syntax

  * The syntax for a typeclass argument (a.k.a. constraint) is now `{| ... |}`
    instead of `[| ... |]`. They are also better supported, and be used in
    `val` declarations and arrows which was not previously the case.

## Module system

  * Friend modules (https://github.com/FStarLang/FStar/wiki/Friend-modules)

## Core typechecker
  * PR https://github.com/FStarLang/FStar/pull/2760 introduces core typechecking for
    implicits introduced for application of indexed effects combinators. This is a
    breaking change, since indexed effects clients are subject to stricter typechecking.

    See the PR description for more details.

  * Cf. #2641, F* now supports only type-based reasoning of reification of indexed
    effects. See https://github.com/FStarLang/FStar/issues/2641 for more discussions
    and associated pull request. This may be a breaking change for clients relying on
    extraction/smt reasoning of indexed effects via reification.

  * F* now supports accessibility predicates based termination proofs. When writing a recursive function

    ```
    let rec x_i : Tot t = ...
    ```

    The decreases metric may be specified as:

    ```
    let rec x_i : Tot t (decreses {:well-founded rel e}) = ...
    ```

    where `rel` is a well-founded relation and `e` is an expression that decreases according to the relation in the recursive calls. See [this PR](https://github.com/FStarLang/FStar/pull/2307) for more details.

  * Since 2686888aab7e8fa7059b61c161ad7a2f867ee1f8, F* no longer
    supports eta equivalence. Dominique Unruh observed that the
    primitive `pointwise` tactic (which treats provable equality as a
    congruence) allows proving functional extensionality, which is
    unsound in conjunction with subtyping in F* (see below for more
    discussion of that). It turns out that a crucial step in that
    unsoundness proof is the use of eta equivalence (See Bug1966a.fst
    for a proof of that, with thanks due there also to Catalin Hritcu,
    who writes about it here
    https://github.com/FStarLang/FStar/wiki/SMT-Equality-and-Extensionality-in-F*).

    To fix this, we removed eta equivalence. One rough intuition for
    why eta reduction is incompatible with subtyping is that it can
    change the type of a function, widening its domain, e.g., for
    `f:int -> int`, reducing `(fun (x:nat) -> f x)` to `f` changes its
    type. Restricting eta reductions to only those that are type
    preserving turns out to not feasible in the presence of
    abstraction and subtyping.

    With the removal of eta, functional extensionality is now a
    theorem in F\* at least for eta-expanded functions, no longer an
    axiom, which is an improvement. The removal of eta equivalence
    introduced regressions in some proofs that were implicitly relying
    on it. See, for example,
    https://github.com/FStarLang/FStar/pull/2294
    and
    https://github.com/project-everest/hacl-star/pull/442

  * PR https://github.com/FStarLang/FStar/pull/2256 and
       https://github.com/FStarLang/FStar/pull/2464 add support for Coq-style
    dependent pattern matching. F* now supports `match e as x returns C with |...`
    syntax for typechecking the branches with `C` appropriately substituted.
    This changes the syntax of the `match` nodes to maintain an optional
    annotation. The data constructor `Tv_Match` in the reflection API changes
    accordingly.

  * Cf. issue https://github.com/FStarLang/FStar/issues/1916,
    F* has a revised treatment for the lexicographic tuples. This is a breaking change
    and may require some additional annotations in the decreases clauses, see for example:
    https://github.com/FStarLang/FStar/pull/2218/commits/0baf2277cd1e2c83ba71c4bc9659f1a84837a33a.
    F* tries to give a warning for such cases that the proof may require type annotations on
    these decreases clause elements.

  * The expected type of the `if_then_else` combinator for layered effects is now
    `a:Type -> bs -> f:repr a is -> g:repr a js -> p:bool -> Type`
    Previously, the `p` parameter used to have type `Type0`. It only needs
    change in the definition of the combinator, no changes are required in
    the client code using the effect. For example, see:
    https://github.com/FStarLang/FStar/commit/731b353aa3bb6c32f4da97170284a1f301b242e1

    The types of the combinators are also subject to stricter typing (no smt and no subtyping).
    See this commit: https://github.com/FStarLang/FStar/commit/a5b2d8818e386b2be1058061a913ffcef4bfb8ea
    for the kind of fixes this change required.

  * Cf. issue https://github.com/FStarLang/FStar/issues/1055,
    F* now enforces that unannotated, effectful functions have a
    trivial precondition (this is already the case for pure functions).

    See some testcases in `examples/bug-reports/Bug1055.fst`.

    The check is performed under a new flag `--trivial_pre_for_unannotated_effectful_fns`,
    which is `true` by-default.

    This is a breaking change, see this commit for how we fixed the F* examples:
    https://github.com/FStarLang/FStar/commit/24bbae4b93a9937695160dff381625adb6565d28

  * Revised typechecking of nested patterns and ascriptions on
    patterns, fixing unsoundnesses (issue #238, for example)

  * NBE: A call-by-value reduction strategy for F* terms is
    implemented using "normalization by evaluation". Specific calls to
    the normalizer (e.g., via `Pervasives.norm`) can request to use
    this reduction strategy by passing the `nbe:norm_step` among the
    reduction steps.

  * Polymonadic binds: See https://github.com/FStarLang/FStar/wiki/Polymonadic-binds

  * Names in the expressions are now annotated with the types at their binding sites
    rather than with the expected types at the use sites. This change resulted in
    a regression in the F* examples:
    https://github.com/FStarLang/FStar/commit/752d457bda9c0a38eef04e71886cc16899d9c13d

    The workaround is an explicit annotation (see comments in the commit above).

  * An unsoundness was discovered and fixed in the treatment of
    lexicographic tuples. In particular, we used to allow relating lex
    tuples of different arity, notably, we had `LexCons _ _ << LexTop`.
    This was intended for the convenience of writing mutual recursive
    functions with decreases clauses using lex tuples of different arities.
    However, this convenience was seldom used and it actually lead to
    an unsoundness: See examples/bug-reports/BugLexTop.fst. This
    variable arity lexicographic tuple ordering is no longer supported.


## Libraries

   * Renamed some of the types in `Prims` in https://github.com/FStarLang/FStar/pull/2461.
       - `c_False` became `empty`
       - `c_True` became `trivial`
       - `c_and` became `pair`
       - `c_or` became `sum`

   * Guido Martinez found that `FStar.WellFounded.axiom1_dep` (and its
     specialization axiom1) is unsound when instantiated across
     different universe levels. The issue and fix is discussed in
     detail here: https://github.com/FStarLang/FStar/issues/2069

     In summary, `FStar.WellFounded.axiom1_dep`,
     `FStar.WellFounded.axiom1`, and `FStar.WellFounded.apply` have
     all been removed. The user-facing universe polymorphic axiom is
     no longer needed---you should just be able to remove calls to it
     in your programs. Instead, we have enhanced F*'s SMT encoding of
     inductive types to include additional, more targeted
     well-foundedness axioms.
     tests/micro-benchmarks/TestWellFoundedRecursion.fst provides
     several small representative examples.

   * Two core axioms were discovered by Aseem Rastogi to be formulated
     in an unsound manner.

     FStar.FunctionalExtensionality has been reformulated to prevent
     equivalence proofs of a function on a given domain to be
     improperly extended to equivalence on a larger domain. The
     library was fixed to ensure that domain type used to prove the
     equivalence was recorded in the axiom. See
     examples/micro-benchmarks/Test.FunctionalExtensionality.fst for
     example uses.

     FStar.PropositionalExtensionality was found to be incompatible
     with the representation of `prop` as the type of all
     sub-singletons. `prop` has been reformulated as the type of all
     sub-types of `unit`.

     See issue #1542 for more discussion.

   * The ulib directory has been restructured with old modules in
     legacy (consider them deprecated), an experimental directory as a
     staging ground, and a .cache directory in which .checked and
     .hints files are maintained.

   * FStar.UInt[N].mul_div has been removed. This operation was not
     supported uniformly, with only an implementation for UInt64
     provided (using UInt128).

## Syntax
   * PR #2812 allows defining variants whose constructors carry
     records, for example:
     ```fstar
     type foo = | A
                | B { x: int; y: int }
     ```

     See `examples/misc/VariantsWithRecords.fst` for more examples.

   * PR #2727 allows for custom unicode operators. As long as a
     character belongs to the ["Math Symbol" unicode
     category](https://www.compart.com/unicode/category/sm), it is
     seen as a right-associative binary operator. Example:
	 ```fstar
	 let ( ∈ ) = List.Tot.memP
	 let _ = assert_norm (3 ∈ [1;2;3;4])
	 ```
	 
	 See `tests/micro-benchmarks/UnicodeOperators.fst` for more
     examples.
    
   * PR #2745 adds support for `if` operators: the syntax `if* a then
     ...` (with `*` an operator) is now accepted and desugared as
     `let* [c] = a in if [c] then ...`.

   * PR #2671 allows operators as field names in record expressions
     and record type declaration. Example:

	 ```fstar
	 type foo = { ( ^ ): int  }
	 let _: foo = { ( ^ ) = 3 }
	 ```

	 See `tests/micro-benchmarks/RecordFieldOperator.fst` for details.

   * PR #2670 makes F*'s parser accept unparenthesised record
     expressions on function application. `f {x = 1}` is now legal
     F\*, while before one was forced to write `f ({x = 1})`.

	   Note that in the context of a (possible) refinement, this is not
     allowed since it is a parser conflict.

   * PR #2669 allows name quotes in patterns, i.e. ``%`foo`` is a
     valid pattern and is desugared to the constant string
     pattern `"X.Y.Z.foo"`, with `X.Y.Z` being `foo`'s module.

   * PR #2686 forbids the sequence `//` in operators. For instance,
     `+//` used to be a legal operator, it is not the case anymore,
     since it is ambiguous with the comment syntax.

   * PR #2644 introduces monadic let operators in the surface
     syntax. One can now write:

	 ```
	 let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
       = match x with
       | Some x -> f x
       | None   -> None

     let foo (x: option (int * option int)) =
	    let? (a, b) = x in
		match? b with
		...
	 ```

     Where `?` is any operator sequence; there is also support for
     `and?`, `;?`, etc. See [example module
     `MonadicLetBindings`](./examples/misc/MonadicLetBindings.fst) for
     more details.

   * PR #2603 introduces universes in the reflection syntax.
     It is a potentially breaking change for reflection clients.
     See the PR for more description.


   * `as` is a keyword now. One use of it is to (optionally) name the
     scrutinee in dependent pattern matching, e.g.:

     ```
     match e as x in t with
     | ...
     ```

     This is a breaking change, code that uses `as` as a variable name
     will require changes (cf. https://github.com/FStarLang/FStar/pull/2464)

   * Type-based disambiguation for projectors and record
     constructors. You can now write:

     ```
     type t = { f : bool }
     type s = { f : bool }
     let test1 (x:t) (y:s) = x.f && y.f
     let test2 (x:t) : s = { f = x.f }
     ```

     Where types are used to disambiguate the field names of `t` and
     `s`. See tests/micro-benchmarks/RecordFieldDisambiguation.fst for
     more examples.

   * `eliminate` and `introduce` are now keywords. They are used to
     implement sugar for manipulating classical logic connectives, as
     documented here:
     https://github.com/FStarLang/FStar/wiki/Sugar-for-manipulating-connectives-in-classical-logic

   * Record opening syntax: Inspired in part by Agda's records as
     modules, you can now write

     ```
     type ty = {x:int; y:bool}

     let f (r:ty) : int =
       let open r <: ty in
       if y then x else -x
     ```

     See tests/micro-benchmarks/RecordOpen.fst for more examples.

   * Support for binder attributes in the reflection APIs `pack_binder`
     and `inspect_binder`. This is a breaking change, see
     https://github.com/project-everest/hacl-star/commit/7a3199c745b69966e54a313e648a275d21686087
     commit for how to fix the breaking code.

   * `abstract` qualifier and the related option `--use_extracted_interfaces`
     are no longer supported. Use interfaces instead.

   * We now overload `&` to construct both dependent and non-dependent
     tuple types. `t1 & t2` is equivalent to `tuple2 t1 t2` whereas
     `x:t1 & t2` is `dtuple2 t1 (fun x -> t2)`. See
     examples/micro-benchmarks/TupleSyntax.fst. The main value
     proposition here is that in contrast to `*`, which clashes with
     the multiplication on integers, the `&` symbol can be used for
     tuples while reserving `*` for multiplication.

   * Attributes are now specified using the notation `[@@ a1; ... ; an]` i.e.,
     a semicolon separated list of terms. The old syntax will soon
     be deprecated.

   * Attributes on binders are now using a different syntax `[@@@ a1; ... ; an]` i.e.,
     @@@ instead of @@. This is a breaking change that enables
     using attributes on explicit binders, record fields and more. See
     https://github.com/FStarLang/FStar/pull/2192 for more details.

## Extraction

   * [PR #2489] Due to the renaming of KReMLin into KaRaMeL,
     `--codegen Kremlin` has been turned into `--codegen krml`, and
     the `(noextract_to "Kremlin")` attribute has been turned into
     `(noextract_to "krml")`. This is a breaking change.

   * Cross-module inlining: Declarations in interfaces marked with the
     `inline_for_extraction` qualifier have their definitions inlined
     in client code. Currently guarded by the --cmi flag, this will
     soon be the default behavior. Also see:
     https://github.com/FStarLang/FStar/wiki/Cross-module-Inlining
     and https://github.com/FStarLang/FStar/tree/master/examples/extraction/cmi.

   * `--use_nbe_for_extraction`: A new option that enables the use of
     the call-by-value normalization-by-evaluation reduction strategy
     for normalizing code prior to extraction.

## SMT Encoding

   * A soundness bug was fixed in the encoding of recursive functions
     to SMT. The flaw resulted from omitting typing guards in the
     axioms corresponding to the equational behavior of pure and ghost
     recursive functions. The fix makes reasoning about recursive
     functions with SMT slightly more demanding: if the typing of an
     application of a recursive functions requires some non-trivial
     proof, the SMT solver may require some assistance with that proof
     before it can unfold the definition of the recursive
     function. For an example of the kind of additional proof that may
     be needed, see these commits:
     https://github.com/FStarLang/FStar/commit/936ce47f2479af52f3c3001bd87bed810dbf6e1f
     and https://github.com/project-everest/hacl-star/commit/2220ab81bbae735495a42ced6485665d9facdb0b.
     We need to call lemmas
     to prove that the recursive function that appears in the
     inductive hypothesis is well-typed
     (e.g. calling `wp_monotone` lemma for well-typedness of `wp_compute` in the second commit) .
     In some cases, it may also be possible to use the normalizer to
     do the unfolding:
     https://github.com/project-everest/hacl-star/commit/6e9175e607e591faa5b6a0d6052fc4a336f7bf41#diff-127ee9d47350eff0fa0d79847257d493R290.
     Another kind of change required hoisting some type declarations:
     https://github.com/FStarLang/FStar/commit/819ad64065f1e70aec3665f5df6b58a7d43cdce1
     to get around imprecision in the SMT encoding. This can be handled in F*
     with an additional SMT axiom on type constructors like `list`, but
     we only found a couple of instances of this. So, for now, we are going with the
     hoisting workaround.

   * The encoding of nullary constants changed. See the documentation
     in https://github.com/FStarLang/FStar/pull/1645

   * An optimization of the SMT encoding removes, by default,
     expensive axioms about validity from the prelude.

     The axiom in question is the following:

     ```
       (assert (forall ((t Term))
                       (! (iff (exists ((e Term)) (HasType e t))
                               (Valid t))
                        :pattern ((Valid t)))))
     ```

     The axiom is justified by our model of squash types and
     effectively capture the monadic structure of squash: the forward
     implication is related to `return_squash` and the backwards
     direction to `bind_squash`.

     However, this axiom is now excluded by default, for two reasons:

     1. The axiom is very expensive for the SMT solver, showing up a
        lot on most SMT profiles. Every occurrence of `Valid t`
        introduces a quantifier in scope (and a skolemized occurrence
        of `HasType e t`).

     2. Most code doesn't actually need these axioms.

     Instead, we now provide two flags to add versions of this axiom
     on demand.

     The option `--smtencoding.valid_intro true` adds the following
     axiom to the prelude:

      ```
        (assert (forall ((e Term) (t Term))
                      (! (implies (HasType e t)
                                  (Valid t))
                       :pattern ((HasType e t)
                                 (Valid t))
                       :qid __prelude_valid_intro)))
      ```

     The option `--smtencoding.valid_elim true` adds the following
     axiom to the prelude:

     ```
       (assert (forall ((t Term))
                      (! (implies (Valid t)
                                  (exists ((e Term)) (HasType e t)))
                       :pattern ((Valid t))
                       :qid __prelude_valid_elim)))
     ```

     Currently, in the F* tree, these axioms are enabled in our
     makefiles (see ulib/gmake/fstar.mk), since a few core libraries
     (FStar.Squash, e.g.) rely on it. But we are working on more
     tightly scoping the use of these axioms in the F* tree.

     Meanwhile, other projects using F* in project-everest no longer
     use these axioms by default.

## Calculational proofs

   * F\* now supports proofs in calculational style, i.e. where an
     equality between two expressions is expressed via a sequence of
     equalities each of which is proven individually. In fact, these
     proofs can be done for any relation, provided that steps compose
     properly (e.g., `a < b == c` implies `a < c`, but `a <= b == c`
     does not imply `a < c`). For some examples, see `examples/calc/`.

## Miscellaneous

   * [Issue #2444](https://github.com/FStarLang/FStar/issues/2444) The
     definition of the type `ident` exposed `FStar.Reflection.Types`
     is now `string * range` instead of `range * string`.

   * Development builds of F\* no longer report the date of the build
     in `fstar --version`. This is to prevent needlessly rebuilding
     F\* even when the code does not change.

## Dependence analysis and build

   * --already_cached provides a way to assert that some modules, and
     only those modules, have already been verified, i.e, valid
     .checked files exist for them. In case a module that is marked
     `--already_cached` does not have a valid .checked file, Error 317
     is raised. Otherwise, if we find a checked file for a module that
     is not already_cached in a location that is not the same as its
     expected output location, we raise Warning 321.

## Command line options
   * F* no longer supports the vcgen.optimize_bind_as_seq command line
			  option for tweaking the verification condition generation.
					The option was not on by-default, and hence was not maintained well.
					Further, as issue #2868 observed, it relied on a strange SMT axiom.

   * [Issue #2385](https://github.com/FStarLang/FStar/issues/2385).
     The behavior of the --extract option was changed so that it no
     longer treats the OCaml and Karamel targets
     differently. Previously, when used with --dep full, F* would
     disregard the --extract setting when emitting the
     `ALL_KRML_FILES` variable.

   * [PR #1711](https://github.com/FStarLang/FStar/pull/1711): Where
     options take lists of namespaces as arguments
     (`--already_cached`, `--extract`, `--using_facts_from`, etc.),
     those lists of namespaces can be given under the form `+A -B +C`
     (space-separated) or `+A,-B,+C` (comma-separated).

   * [PR #1985](https://github.com/FStarLang/FStar/pull/1985): The
     `--profile` flag changed to take instead a set of modules on
     which to enable profiling. The output of F* on its finished
     message changed to not print the time it took to verify a module.

   * [PR #2776](https://github.com/FStarLang/FStar/pull/2776): The
     `--split_queries` option now takes an argument, one of `no`,
     `on_failure` and `always`. The default is `on_failure`, with
     the same behavior as previously (split a query and retry when
     the SMT solver does not return a helpful error). Using
     `--split_queries always` mimics the old `--split_queries`,
     splitting all queries eagerly. Using `--split_queries no` disables
     splitting altogether.

## Editors

   * Support for vscode via LSP (https://github.com/FStarLang/FStar/wiki/Using-F*-with-vscode)

# Version 0.9.6.0

## Command line options

   `--use_two_phase_tc` is no longer a command line option.

   F* reads .checked files by default unless the `--cache_off` option is provided.
   To write .checked files, provide `--cache_checked_modules`

   `--use_two_phase_tc true` is now the default. This improves type
   inference for implicit arguments and reduces our trust in type
   inference, since the result of type inference is type-checked
   again.

   `--use_extracted_interfaces` now takes a boolean string as an
   option, i.e., `--use_extracted_interfaces true` or
   `--use_extracted_interfaces false`. The latter is the default. The
   next release of F* aims to turn this on always with no option to
   turn it off. This feature is more demanding in enforcing
   abstraction at module boundaries; without out it, some abstractions
   leak. See
   https://github.com/FStarLang/FStar/wiki/Revised-checking-of-a-module's-interface
   for more information.

   `--keep_query_captions true|false` (default `true`) when set to `true`,
   and when `--log_queries` is enabled, causes .smt2 files to be logged with
   comments; otherwise comments are not printed. Note, the comments
   can be quite verbose.

   `--already_cached "(* | [+|-]namespace)*"`, insists that .checked files be
   present or absent for modules that match the namespace pattern provided.

   `--smtencoding.valid_intro` and `--smtencoding.valid_elim`: See PR
   #1710 and the discussion above in the SMT encoding section.

## Type inference

   We had a significant overhaul of the type inference algorithm and
   representation of unification variables. The new algorithm performs
   significantly better, particularly on memory consumption.

   But, some of the heuristics changed slightly so you may have to add
   annotations to programs that previously required none.

   For the changes we had to make to existing code, see the commits
   below:

```
commit d4c0161c22ab9ac6d72900acd7ed905d43cb92b7
Author: Nikhil Swamy <nikswamy@users.noreply.github.com>
Date:   Tue May 8 15:27:19 2018 -0700

    ***SOURCE CODE CHANGE*** in support of new inference; need an annotation in Synthesis.fst


commit 362fa403c45def14fb2e2809e04405c39e88dfcb
Author: Nikhil Swamy <nikswamy@users.noreply.github.com>
Date:   Tue May 1 15:55:08 2018 -0700

    ***SOURCE CODE CHANGE*** for inference; the inferred type is more precise than previously, which leads to failure later; annotated with a weaker type

commit ec17efe04709e4a6434c05e5b6f1bf11b033353e
Author: Nikhil Swamy <nikswamy@users.noreply.github.com>
Date:   Mon Apr 30 22:11:54 2018 -0700

    ***SOURCE CODE CHANGE** for new inference; a repacking coercion needs an annotation

commit f60cbf38fa73d5603606cff42a88c53ca17fbd37
Author: Nikhil Swamy <nikswamy@users.noreply.github.com>
Date:   Mon Apr 30 22:11:17 2018 -0700

    ***SOURCE CODE CHANGE*** for new inference; arguably an improvement

commit c97d42cae876772a18d20f54bba2a7d5fceecd69
Author: Nikhil Swamy <nikswamy@users.noreply.github.com>
Date:   Mon Apr 30 20:59:50 2018 -0700

    **SOURCE CODE CHANGE** for new type inference; arguably an improvement

commit 936a5ff7a8404c5ddbdc87d0dbb3a86af234e71b
Author: Nikhil Swamy <nikswamy@users.noreply.github.com>
Date:   Mon Apr 30 16:57:21 2018 -0700

    ***SOURCE CODE CHANGE*** for type inference; could be reverted once prop lands
```


# Version 0.9.6.0~alpha1

## Syntax

* The syntax of type annotations on binders has changed to eliminate a
  parsing ambiguity. The annotation on a binder cannot itself contain
  top-level binders. For example, all of the following previously
  accepted forms are now forbidden:

  ```
    let g0 (f:x:a -> b) = ()
    let g1 (f:x:int{x > 0}) = ()
    let g2 (a b : x:int{x> 0}) = ()
    let g3 (f:a -> x:b -> c) = ()
   ```

  Instead, you must write:


  ```
    let g0 (f: (x:a -> b)) = ()
    let g1 (f: (x:int{x > 0})) = ()
    let g2 (a b : (x:int{x> 0})) = ()
    let g3 (f : (a -> x:b -> c)) = ()
   ```

  In the second case, this version is also supported and is preferred:

  ```
    let g1 (f:int{f > 0}) = ()
  ```

  See the following diffs for some of the changes that were made to
  existing code:

  https://github.com/FStarLang/FStar/commit/6bcaedef6d91726540e8969c5f7a6a08ee21b73c
  https://github.com/FStarLang/FStar/commit/03a7a1be23a904807fa4c92ee006ab9c738375dc
  https://github.com/FStarLang/FStar/commit/442cf7e4a99acb53fc653ebeaa91306c12c69969

## Basic type-checking and inference

* A revision to implicit generalization of types
    (Since [commit FStar@e15c2fa4eb4cd7a10dd74fc5532b6cac8e23b4f1])

  F* has for a while supported implicit generalization of types in
  support of ML-style, let-polymorphism. E.g., `let id x = x` would
  have the implicitly generalized type `#a:Type -> a -> Tot a`.

  However, F* would incorrectly also allow implicitly generalizing
  over variables of types other than `Type`. For example, this program
  would type-check, at a rather counter-intuitive type.

  ```
  type empty (x:False) =
  let rec t (#x:False) (n:nat) : empty x = t #x n
  let f () = t 0
  ```

  where, `f` would be given the type `#x:False -> unit -> empty x`.

  Worse, sometimes F* would generalize over types with free variables,
  leading to crashes as in bug #1091.

  We now restrict implicit generalization to variables whose type is a
  closed refinement of `Type`, e.g.,
    `let id x = x` has the same type as before;
    `let eq = op_Equality` has the type `#a:eqtype -> a -> a -> bool`;
     etc.

  This restriction is a breaking change. For a sampling of the changes
  needed to accommodate it see:

       [commit mitls/hacl-star@c93dd40b89263056c6dec8c606eebd885ba2984e]
       [commit FStar@8529b03e30e8dd77cd181256f0ec3473f8cd68bf]

* More predictable and uniform inlining behavior when computing wps

  When computing wp of `let x = e1 in e2`, F* computes the wp of `e1`,
  say `wp1`, and that of `e2`, say `wp2` (where `x` is free in
  `wp2`), and binds the twp wps to get the final wp.

  Earlier the typechecker would perform inlining of `e1` in `wp2` in
  certain cases (i.e. `wp2[e/x]`), e.g. when both `e1` and `e2` are
  `Tot`, or both `e1` and `e2` are `GTot`, etc. If none of these
  optimizations applied, the typechecker would simply use the
  effect-specific `bind` to compute the final wp. This behavior was
  quite brittle. See PR 1350 for an example.

  Now the typechecker follows a more uniform, and predictable inlining
  strategy. Term `e1` is inlined into `wp2` if all the following
  conditions hold:

  1. `e1` is a `Pure` or `Ghost` term
  2. The return type of `e1` is not `unit`
  3. The head symbol of `e1` is not marked `irreducible` and it is not an `assume val`
  4. `e1` is not a `let rec`

  This is a breaking change. Consider the following example (adapted
  from `ulib/FStar.Algebra.Monoid.fst`):

  ```
  let t (m:Type) (u:m) (op:m -> m -> m) =
    forall (x:m). x `op` u == x

  let foo :unit =
    let u : prop = True in
    let conj (p q : prop) : prop = p /\ q in
    assume (forall (p:prop). p `conj` u == p);  //extensionality of props
    assert (t prop u conj) ;
    ()
  ```

  Previously, the inlining of `u` and `conj` didn't kick in, and so,
  when the query goes to Z3, the `assume` remains in the precondition
  of the query, and Z3 is able to then prove `p /\ True == p`.

  With the new inlining behavior, `u` and `mult` get inlined, and the
  assumption then becomes `p /\ True == p`. Before giving it to Z3,
  the normalizer simplifies `p /\ True` to `squash p` (roughly, see PR
  380), and then Z3 is no longer able to prove the query.

  To get around this inlining behavior, `prims` now provides a
  `singleton` function. Wrapping `u` in `singleton` like:

  ```
    ...
    let u : prop = singleton True in
    ...
  ```

  prevents inlining of `u`, leaving the assumption as is for Z3.

  See [commit
  FStar@02707cd0](https://github.com/FStarLang/FStar/commit/02707cd037f1d297452bb150c7a7e84dc11d5ee7)
  for an example.

  Only `ulib/FStar.Algebra.Monoid.fst` needed to be tweaked like this.

## IDE

* F* now prints `progress` messages while loading dependencies in `--ide` mode
  (https://github.com/FStarLang/FStar/commit/084638c12ae83ecfa975abd6bbc990f6a784a873)

* Sending an interrupt (C-c / SIGINT) to F* in `--ide` mode does not kill the
  process any more.  Instead, it interrupts the currently running query or
  computation.  Not all queries support this (at the moment only `compute` and
  `push` do); others simply ignore interrupts
  (https://github.com/FStarLang/FStar/commit/417750b70ae0d0796a480627149dc0a09f9437d2).
  This feature is experimental.

* The `segment` query can now be used to split a document into a list of
  top-level forms.

* Some `proof-state` messages now contain location information.

## Standard library

* Related to the change in implicit generalization of types, is the
  change to the standard libraries for state.

  This program is no longer accepted by F*:

  ```
  module Test
  open FStar.ST
  let f x = !x
  ```

  It fails with:

  ```
  test.fst(4,0-4,12):
        (Error) Failed to resolve implicit argument of type
        'FStar.Preorder.preorder (*?u538*) _'
         in the type of f
         (x:FStar.ST.mref (*?u538*) _ (*?u542*) _ -> FStar.ST.STATE (*?u538*) _)
  ```

  This is because `FStar.ST` is now designed to work with monotonic
  references which are indexed by preorders.

  If you do not intend to use preorders, open `FStar.Ref` instead. The
  program below is accepted.

  ```
  module Test
  open FStar.Ref
  let f x = !x
  ```

* FStar.Char.char: In support of unicode, FStar.Char.char is now an
  abstract alias for a 21 bit integer represented within a
  FStar.UInt32.t.

* contrib/Platform/fst/*: These modules are deprecated. Their
  functionality is now moved to FStar.Bytes, FStar.Error, FStar.Tcp,
  FStar.Udp, and FStar.Date.

* Implentation of the HyperStack memory model and monotonic libraries
  (refs, sequences, and maps)


  1. `Monotonic.RRef` is gone. Following is the mapping of the
     functions that have been removed (`MR` is `Monotonic.RRef`, `HS`
     is `FStar.HyperStack`, `HST` is `FStar.HyperStack.ST`):

     1.  `MR.reln a` --> `Preorder.preorder a`
     2.  `MR.monotonic a b` --> `Preorder.preorder_rel a b`
     3.  `MR.m_rref r a b` --> `HST.m_rref r a b`
     4.  `MR.as_hsref` --> this coercion is not needed anymore
     5.  `MR.m_contains r m` --> `HS.contains m r`
     6.  `MR.m_fresh r m0 m1` --> `HS.fresh_ref r m0 m1`
     7.  `MR.m_sel m r` --> `HS.sel m r`
     8.  `MR.m_alloc r init` --> `HST.ralloc r init`
     9.  `MR.m_read r` --> `!r` (where `!` is defined in `HST`)
     10. `MR.m_write r x` --> `r := x` (where `:=` is defined in `HST`)
     11. `MR.witnessed p` --> `HST.witnessed p`
     12. `MR.m_recall r` --> `HST.recall r`
     13. `MR.rid` --> `HST.erid`
     14. `MR.witness` --> `HST.mr_witness`
     15. `MR.testify` --> `HST.testify`
     16. `MR.testify_forall` --> `HST.testify_forall`
     17. `MR.ex_rid` --> `HST.ex_rid`
     18. `MR.ex_rid_of_rid` --> `HST.witness_region`

     See the following commits for examples:

     https://github.com/mitls/mitls-fstar/commit/be1b8899a344e885bd3a83a26b099ffb4184fd06
     https://github.com/mitls/mitls-fstar/commit/73299b71075aca921aad6fbf78faeafe893731db
     https://github.com/mitls/hacl-star/commit/1fb9727e8193e798fe7a6091ad8b16887a72b98d
     https://github.com/mitls/hacl-star/commit/c692487d970730206d1f3120933b85d46b87f0a3


  2. `HyperStack` references (`reference, mref, stackref, ...` etc.)
     are now defined in `FStar.HyperStack.ST`. So, the clients must
     `open` `FStar.HyperStack.ST` after `FStar.HyperStack` so that the
     correct ref types are in the context. If the clients also open
     `FStar.Monotonic.RRef`, then it can be opened after
     `FStar.HyperStack.ST`, since it defines its own ref type.

  3. When allocating a new region or a reference, the caller has to
     now satisfy a precondition `witnessed (region_contains_pred r)`,
     where `r` is the parent region. If `r` is an eternal region, this
     predicate can be obtained using the
     `HyperStack.ST.witness_region` function (by showing that the
     region is contained in the memory). See for example:

     https://github.com/FStarLang/FStar/commit/29c542301e2589d76869b4663b9b21884ea9fcfa#diff-eaa8cd4efc632ac485423c4eae117fedR208

     Further, in some cases ref allocation may need some annotation
     about the default, trivial preorder (see the change regarding
     implicit generalization of types above). For example:

     https://github.com/FStarLang/FStar/commit/f531ce82a19aa7073856cea8dd14fa424bbdd5dd#diff-86e8502a719a3b2f58786f2bdabc4e75R491

  4. `FStar.Monotonic.HyperStack.is_eternal_region` is
     deprecated. Client should instead use
     `FStar.HyperStack.ST.is_eternal_region`. To migrate the code, the
     script `renamings.sh` in `FStar/.scripts` can be used as:
     `renamings.sh replace "HS\.is_eternal_region" "is_eternal_region"`.
     Most of the stateful code already includes `FStar.HyperStack.ST`,
     so the above should just work. This change simplifies the point 3
     above, in that there is no extra proof obligation when creating
     regions now.

  5. `FStar.HyperStack.mem` is now `abstract`. The client changes include
     the following mappings (where `h` has type `mem`):

     1. `h.tip` --> `HS.get_tip h`
     2. `h.h` --> `HS.get_hmap h`

     The script `FStar/.scripts/renamings.sh` has a new option
     `rename_hs_mem_projectors` that tries to do this renaming
     in all the `fst` and `fsti` files. If you use this script,
     make sure the gloss over the renamings (using `git diff`) to
     see that the changes are fine.

     The change is only syntactic in the clients, there shouldn't
     be any other proof changes.

* Consolidation of HyperHeap and HyperStack memory models, and
  corresponding APIs for `contains`, `modifies`, etc.

  Client should now only work with `FStar.HyperStack`, in fact `open
  FStar.HyperHeap` will now give an error. Following is a (partial)
  mapping from `HH` (`HyperHeap`) API \to `HS` (`HyperStack`) API:

  1. `HH.contains_ref` --> `HS.contains`
  2. `HH.fresh_rref` --> `HS.fresh_ref`
  3. `HH.fresh_region` --> `HS.fresh_region`
  4. `HH.modifies` --> `HS.modifies_transitively`
  5. `HH.modifies_just` --> `HS.modifies`
  6. `HH.modifies_one` --> `HS.modifies_one`
  7. ...

  For a complete list of the mapping implemented as a crude script to
  rewrite source files, see:
  https://github.com/mitls/mitls-fstar/blob/quic2c/src/tls/renamings.sh

  `HyperHeap` now only provides the map structure of the memory, and
  is `include`d in `HyperStack`, meaning client now get `HS.rid`,
  `HS.root`, etc. directly.

  There is no `HyperHeap.mref` anymore. `HyperStack` refs are
  implemented directly over `Heap.mref`, which means,
  `HS.mk_mreference` now takes as argument `Heap.mref`, and there is
  no `HS.mrref_of` function anymore.

  The `HyperStack` API has also been consolidated. Different versions
  of API (`weak_contains`, `stronger_fresh_region`, etc.) are not
  there anymore.

  There is one subtle change. The `HS.modifies` functions earlier also
  established `m0.tip == m1.tip`, where `m0` and `m1` are two `HS`
  memories. This clause is no longer there, it seemed a bit misplaced
  in the `modifies` clauses. It also meant that if the clients wanted
  to talk only about modified refs, regions, etc. without getting into
  tip, they had to use `HH` functions (e.g. in `Pointer`). With this
  clause no longer there, at some places, `m0.tip == m1.tip` had to be
  added separately in postconditions, e.g. see the commit in HACL*
  below. But note that this should be quite easy to prove, since the
  `ST` effect provides this directly.

  https://github.com/mitls/hacl-star/commit/f83c49860afc94f16a01994dff5f77760ccd2169#diff-17012d38a1adb8c50367e0adb69c471fR55

## Extraction

* Pure terms are extracted while preserving their local `let`-structure.
This avoids code blow-up problems observed in both HACL and miTLS.
To recover the old behavior, at the cost of larger code size,
use the option `--normalize_pure_terms_for_extraction`.
Changed since 45a120988381de410d2c1c5c99bcac17f00bd36e

* Since 393835080377fff79baeb0db5405157e8b7d4da2, erasure for
  extraction is substantially revised. We now make use of a notion of
  "must_erase" types, defined as follows:

   ```
   must_erase ::= unit
               | Type
               | FStar.Ghost.erased t
               | x:must_erase{t'}            //any refinement of a must_erase type
               | t1..tn -> PURE must_erase _ //any pure function returning a must_erase type
               | t1..tn -> GHOST t' _        //any ghost function
   ```

  Any must_erase type is extracted to `unit`.
  Any must_erase computation is extracted as `()`.
  A top-level must_erase computation is not extracted at all.

## Command line options

* --verify_all, --verify_module, --extract_all, --explicit_deps are
    gone. The behavior of `--dep make` has changed. See the section on
    dependence analysis below.

## Dependence analysis; which files are verified and extracted

* When a file `f` (either an implementation or an interface file)
  refers to a symbol from a module `A`, then `f` depends only on the
  interface of `A` if one exists on the search path. If no interface
  exists for `A` then `f` depends on the implementation of `A`.

* Additionally, an implementation file always depends on its
  interface, if one exists. An interface does not depend on its
  implementation.

* The `--dep full` option:

  Invoking `fstar --dep full f1 ... fn`

     - emits the entire dependence graph D of `f1 ... fn`

     - additionally, for every interface file `a.fsti` in D whose
       implementation `a.fst` is not in D, we also emit the
       dependence graph of `a.fst`.

  This means, for instance, that you can run `fstar --dep full` on all
  the root files of your project and get dependences (in make format)
  for all the files you need to verify in order to be sure that your
  project is fully verified.

* When you invoke `fstar f1 ... fn`, the only files that are verified
  are those that are mentioned on the command line. The dependences of
  those files are computed automatically and are lax-checked.

* Given an invocation of `fstar --codegen OCaml f1 ... fn`, all (and
  only) implementation files in the dependence graph of `f1 ... fn`
  will be extracted.

* The `--expose_interfaces` option:

  In rare cases, we want to verify module `B` against a particular,
  concrete implementation of module `A`, disregarding the abstraction
  imposed by an interface of `A`.

  In such a situation, you can run:

     `fstar --expose_interfaces A.fsti A.fst B.fst`

  Note, this explicitly breaks the abstraction of the interface
  `A.fsti`. So use this only if you really know what you're doing.

* We aim to encourage a style in which typical invocations of `fstar`
  take only a single file on the command line. Only that file will be
  verified.

* Only that file will be verified and extracted (if --codegen is
  specified).

* The --cache_checked_modules flag enables incremental, separate
  compilation of F* projects. See examples/sample_project for how this
  is used.

Expected changes in the near future:

* We will make --cache_checked_modules the default so that the cost of
  reloading dependences for each invocation of fstar is mininimized.

* The --extract_namespace and --extract_module flags will be removed.

## Error reporting

* Every error or warning is now assigned a unique number. Error
  reports now look like this:

```
.\test.fst(2,22-2,23): (Error 19) Subtyping check failed; expected type Prims.nat; got type Prims.int (see also D:\workspace\everest\FStar\ulib\prims.fst(316,17-316,23))
```

  Notice the `19`: that's the unique error number.

  Warnings can be silenced or turned into errors using the new
  `--warn_error` option.

## Tactics

* Let bindings are now part of the reflected syntax (Tv_Let), and can be
  inspected/created in the usual manner.

* New primitive: `launch_process` which runs an external command
  and returns its output. For security reasons, this only works if
  `--unsafe_tactic_exec` is provided (which can only be set externally).

* New primitive: `norm_term` to call the normalizer on a quoted term.

* [commit
  FStar@06948088](https://github.com/FStarLang/FStar/commit/0694808861d2428b2a552e3291c643b2d13b2fcc)
  The tactics normalization interface is now on par with the normalization
  available to the type checker. This included some backwards-incompatible
  changes to how reduction steps are referenced in tactics. See [the changes to
  Normalization.fst](https://github.com/FStarLang/FStar/commit/0694808861d2428b2a552e3291c643b2d13b2fcc#diff-a06134671d813bd28252d8520210edb5)
  for some examples. The biggest breaking change is that `UnfoldOnly` (which
  used to take a `list fv`) has been replaced with `delta_only`, which takes a
  list of fully-qualfied identifiers (eg, `FStar.Map.map`). The other reduction
  steps are nullary and have simply been renamed.

* `clear`, which removed the innermost binder from the context, now takes a binder as
   an argument an will attempt to remove it from any position (given that dependency allows it).
   The old behaviour can be recovered with `clear_top` instead.

# Version 0.9.5.0

## Standard library

* [commit FStar@f73f295e](https://github.com/FStarLang/FStar/commit/f73f295ed0661faec205fdf7b76bdd85a2a94a32) The specifications for the machine integer libraries (`Int64.fst`,
  `UInt64.fst`, etc) now forbid several forms of undefined behavior in C.

  The signed arithmetic `add_underspec`, `sub_underspec`, and `mul_underspec`
  functions have been removed.

  Shifts have a precondition that the shift is less than the bitwidth.

  Existing code may need additional preconditions to verify (for example, see
  a
  [fix to HACL*](https://github.com/mitls/hacl-star/commit/c8a61ab189ce163705f8f9ff51e41cab2869f6d6)).
  Code that relied on undefined behavior is unsafe, but it can be extracted
  using `assume` or
  `admit`.

## C Extraction

* [PR #1176](https://github.com/FStarLang/FStar/pull/1176)
  `inline_for_extraction` on a type annotation now unfolds it at extraction
  time. This can help to reveal first-order code for C extraction;
  see [FStarLang/karamel #51](https://github.com/FStarLang/karamel/issues/51).

## Command line options

* --hint_stats and --check_hints are gone
    b50c88930e3f2655704696902693941525f6cf9f. The former was rarely
    used. The latter may be restored, but the code was too messy to
    retain, given that the feature is also not much used.

* --hint_info and --print_z3_statistics are deprecated. They are
    subsumed by --query_stats.

* --cache_checked_modules: writes out a .checked file from which the
  typechecker can reconstruct its state, instead of re-verifying a
  module every time

## Error reporting

* The error reports from SMT query failures have been substantially
  reworked. At least a diagnostic (i.e., an "Info" message) is issued
  for each SMT query failure together with a reason provided by the
  SMT solver. To see that diagnostic message, you at least need to
  have '--debug yes'. Additionally, localized assertion failures will
  be printed as errors. If no localized errors could be recovered
  (e.g., because of a solver timeout) then the dreaded "Unknown
  assertion failed" error is reported.

* --query_stats now reports a reason for a hint failure as well as
  localized errors for sub-proofs that failed to replay. This is
  should provide a faster workflow than using --detail_hint_replay
  (which still exists)

## Miscellaneous

* A file can now contain at most one module or interface
