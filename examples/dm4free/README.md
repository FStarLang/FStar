Dijkstra Monads for Free
------------------------

Run it with:

```
fstar --trace_error --debug_level ED --debug FStar.DM4F.Test FStar.DM4F.Test.fst --prn --print_implicits --print_universes --lax --print_bound_var_types
```

Current status:
- `repr`, `bind` and `return` are *-transformed and _-elaborated;
- same goes for the actions.

The code is in `src/tc/dmff.fs`.
- `star_type_definition` is the *-transformation from the paper for types;
- `star_expr_definition` performs the *-transformation and the _-elaboration at
  the same time; it relies on the bidirectional inference / synthesis engine
  (`infer` and `check`); details currently in a .txt note in our private
  repository.
- `trans_F` and `trans_G` are the `F_C(wp)` and `G^\epsilon_H` helpers from the
  paper
- `gen_wps_for_free` uses "stronger than" to generate more combinators;
  specifically, it generates `if_then_else`, `assert`, `assume`, `close`; it
  also generates `trivial` but the term is (at the time of this writing)
  ill-formed.

The output of the *-transformation and the _-elaboration is re-checked (the
generated terms are well-formed in F*); the effect definition is lifted from DM
to F*; missing WPs are generated, and everything is sent off to the "regular"
effect checking code, where it currently fails.

Items left:
- fill out various TODOs in `dmff.fs` to faithfully check everything (right now,
  most checks are fairly lax);
- clean up `gen_wps_for_free`; use `tc_decl` to declare all the combinators as
  top-level names that are first well-typed; then, normalize them;
- instead of using macros, use applications of these toplevel names;
- debug why `trivial` is ill-typed;
- fix F*'s type-checker to deal with curried vs non-curried (should fix the
  current failure)
- generate the missing WP combinators (`ite_wp`, `stronger`, `null_wp`)
- try out more things in the definition language; try out with a parameterized
  `STATE (h: heap)` effect; etc.
