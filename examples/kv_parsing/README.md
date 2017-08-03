# Low-level parsing

Experiments in low-level parsing that extracts to reasonable C code, proves correctness against a pure specification, and includes support for serialization.

# TODO

## KreMLin features

* `interruptible_for` for both `validate_many_st` and `lookup` (see [FStarLang/kremlin#49](https://github.com/FStarLang/kremlin/issues/49))
* `inline_for_extraction` for types (specifically, functions which compute types) should be unfolded by extraction (eg, `serializer_any`). `unfold` works for extraction but breaks verification
* `must_extract` annotation to fail if something doesn't extract, and potentially block CI
* add a checkout of kremlin and set `KREMLIN_HOME` on CI so `C.Loops.fst` and `C.fst` are available
* `C.fst` needs specs for big endian reading/encoding (fix known - HACL* already did this but not in the KreMLin library)
* KreMLin extraction doesn't have `memcmp` (see [FStarLang/kremlin#50](https://github.com/FStarLang/kremlin/issues/50))
* might need a generic `while` loop; mine will terminate, but the proof will be a bit tricky (local offset will eventually reach the input buffer length)

## Extraction bugs

* looks like `[@"substitute"]` consistently fails when applied two levels deep; potential examples:
   * `ser_append` never works (see `ser_u16_array`, `ser_entry`, and `ser_numbers`)
   * `for_readonly` doesn't work for `validate_many_st` in `validate_entries`
* `for_readonly2` doesn't work for `lookup` (possibly distinct from previous issue; I don't think there's nesting in this example)
* `validate_numbers_data` and `ser_numbers_data` are ambiguous but currently extract to returning function pointers; this isn't the behavior I want
