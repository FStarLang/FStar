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
