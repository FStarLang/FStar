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
