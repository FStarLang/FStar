Dijkstra Monads for Free
------------------------

The (boring) example:

```
fstar FStar.DM4F.Test.Fst
```

To see more debug output, and see the generated combinators:

```
fstar --trace_error --debug_level ED --debug FStar.DM4F.Test FStar.DM4F.Test.fst --prn --print_implicits --print_universes --print_bound_var_types
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
effect checking code.

Items left:
- fill out various TODOs in `dmff.fs` to faithfully check everything (right now,
  most checks are fairly lax);
- generate the missing WP combinators (`ite_wp`, `null_wp`)
- try out more things in the definition language; try out with a parameterized
  `STATE (h: heap)` effect; etc
- figure out how to properly type-check actions (right now, the code is
  suboptimal);
- write get and put in direct style, reify them, then copy the things from intST
  into the test file.
