# Low-level parsing

Experiments in low-level parsing that extracts to reasonable C code, proves correctness against a pure specification, and includes support for serialization.

# Results

- `parser` works out nicely for specifications
- `stateful_validator` is easy to write but needs to match parser structure to prove
    - big issue of changing parser in type of a stateful validator
    - extrinsic proofs would make it much easier to inject these lemmas automatically
    - rather than parsers as type indices, using extrinsic facts would help customize automation
    - run into [issue #65](https://github.com/FStarLang/FStar/issues/65): cannot subtype parser t and parser t' (need an identity function to coerce, and hard to inline this function away since it pattern matches an option)
    - need to change type indices to "equivalent" parsers (generally, functional extensionality for parsers, but here actually any parsers that are "equi-valid", _ie_, valid for the same inputs)
    - `then_check` is nearly useless due to extra spec-only arguments and lack of inference. Careful annotation of parameters with `$` combined with adjusting the return type with a coercion would alleviate this problem.
- `serializer_any` is complicated by need for framing of input buffers in specification
    - while definition is gnarly, proving that framing isn't so hard (first of all, have constant sets of input buffers)
    - `ser_append` has some annoying proof obligations from a lack of appropriate triggers. This isn't actually a problem since it can be provided by the library.
- validated access sounds very good in theory, but framing for iterators was quite challenging
    - recursive versions did eventually verify
    - loops were much harder to prove against recursive specs
    - framing with loops that mutate buffers never worked out nicely
- `ser_append` requires normalization for extraction and higher-order code for verification
- serializing an enum requires eta expansion under match branches for extraction and higher-order code for verification
  - Proposed solution: allow tactic at extraction time to type check against desired type but produce any proven equivalent stateful function for implementation. Replaces hacks and augments extraction with a powerful, generic mechanism. Example of eta expansion demonstrates that pure normalization is insufficient to generate Low* code.

# TODO

## KreMLin features

* Support `must_extract` annotation to fail if something doesn't extract, and potentially block CI.
* Backport fixes to integer functions in `C.fst` and `FStar.Kremlin.Endianness.fst` and (at least model) `C.Loops.do_while` to kremlin master for CI.

## Extraction bugs

* looks like `[@"substitute"]` consistently fails when applied two levels deep; potential examples:
   * `ser_append` never works (see `ser_u16_array`, `ser_entry`, and `ser_numbers`)
   * `for_readonly` doesn't work for `validate_many_st` in `validate_entries`
* `for_readonly2` doesn't work for `lookup` (possibly distinct from previous issue; I don't think there's nesting in this example)
* `validate_numbers_data` and `ser_numbers_data` need to be eta-expanded for extraction but this breaks verification.
