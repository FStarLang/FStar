# Low-level parsing

Experiments in low-level parsing that extracts to reasonable C code, proves correctness against a pure specification, and includes support for serialization.

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
