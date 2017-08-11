# Low-level parsing

Experiments in low-level parsing that extracts to reasonable C code, proves correctness against a pure specification, and includes support for serialization.

# TODO

## KreMLin features

* `must_extract` annotation to fail if something doesn't extract, and potentially block CI
* ~~add a checkout of kremlin and set `KREMLIN_HOME` on CI so `C.Loops.fst` and
  `C.fst` are available~~
* ~~might need a generic `while` loop. Modeled in kremlin branch `schema_21` (no
  implementation)~~
* ~~`C.fst` needs specs for big endian reading/encoding - fixed in kremlin
  branch `schema_21` by porting Hacl*'s work.~~
* ~~`inline_for_extraction` for types (specifically, functions which compute
  types) should be unfolded by extraction (eg, `serializer_any`). `unfold` works
  for extraction but breaks verification. Fixed by
    [FStarLang/FStar#1176](https://github.com/FStarLang/FStar/pull/1176).~~

## Extraction bugs

* looks like `[@"substitute"]` consistently fails when applied two levels deep; potential examples:
   * `ser_append` never works (see `ser_u16_array`, `ser_entry`, and `ser_numbers`)
   * `for_readonly` doesn't work for `validate_many_st` in `validate_entries`
* `for_readonly2` doesn't work for `lookup` (possibly distinct from previous issue; I don't think there's nesting in this example)
* `validate_numbers_data` and `ser_numbers_data` are ambiguous but currently extract to returning function pointers; this isn't the behavior I want
