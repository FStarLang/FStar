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

  This is breaking change. Consider the following example (adapted
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

## Standard library

* [commit FStar@f73f295e](https://github.com/FStarLang/FStar/commit/f73f295ed0661faec205fdf7b76bdd85a2a94a32)

  The specifications for the machine integer libraries (`Int64.fst`,
  `UInt64.fst`, etc) now forbid several forms of undefined behavior in
  C.

  The signed arithmetic `add_underspec`, `sub_underspec`, and `mul_underspec`
  functions have been removed.

  Shifts have a precondition that the shift is less than the bitwidth.

  Existing code may need additional preconditions to verify (for example, see
  a
  [fix to HACL*](https://github.com/mitls/hacl-star/commit/c8a61ab189ce163705f8f9ff51e41cab2869f6d6)).
  Code that relied on undefined behavior is unsafe, but it can be extracted
  using `assume` or
  `admit`.

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

* ucontrib/Platform/fst/*: These modules are deprecated. Their
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


## C Extraction

* [PR #1176](https://github.com/FStarLang/FStar/pull/1176)
  `inline_for_extraction` on a type annotation now unfolds it at extraction
  time. This can help to reveal first-order code for C extraction;
  see [FStarLang/kremlin #51](https://github.com/FStarLang/kremlin/issues/51).

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

* Every error or warning is now assigned a unique number. Error
  reports now look like this:

```
.\test.fst(2,22-2,23): (Error 19) Subtyping check failed; expected type Prims.nat; got type Prims.int (see also D:\workspace\everest\FStar\ulib\prims.fst(316,17-316,23))
```

  Notice the `19`: that's the unique error number.
  
  Warnings can be silenced or turned into errors using the new
  `--warn_error` option.
   
## Miscellaneous

* A file can now contain at most one module or interface

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
