DISCLAIMER
----------

This branch has been merged into master and will be deleted soon. Nothing new
will happen here! For the latest developments of Dijkstra Monads for Free,
please check out this very directory in the master branch.

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
effect checking code.

Items left:
- fill out various TODOs in `dmff.fs` to faithfully check everything (right now,
  most checks are fairly lax);
- generate the missing WP combinators (`ite_wp`, `null_wp`)
- try out more things in the definition language; try out with a parameterized
  `STATE (h: heap)` effect; etc
- re-instate the optimization in [env.fs] when checking for universe variables
  in [gamma]
- figure out how to properly type-check actions (right now, the code is
  suboptimal);
- figure out why the commented out assert in [tc_eff_decl] is failing;
- write get and put in direct style, reify them, then copy the things from intST
  into the test file.
