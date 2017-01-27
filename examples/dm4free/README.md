Dijkstra Monads for Free
------------------------

Examples associated to this paper:
https://www.fstar-lang.org/papers/dm4free/

Any `FStar.DM4F.*` file successfully verifies.

To try out a basic, complete example:

```
fstar.exe FStar.DM4F.IntSt.Fst
```

To see the generated combinators (look for top-level definitions starting with
`FStar.DM4F.Test.STINT_`):

```
fstar.exe --dump_module FStar.DM4F.IntST FStar.DM4F.IntST.fst
```

To see more debug output related to the DMFF elaboration and star
transformations:

```
fstar.exe --trace_error --debug_level ED --debug FStar.DM4F.IntST FStar.DM4F.IntST.fst --prn --print_implicits --print_universes --print_bound_var_types
```

Current status:
- `repr`, `bind` and `return` are *-transformed and _-elaborated;
- same goes for the actions;
- all the remaining combinators are generated.

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
  also generates `trivial`.

The output of the *-transformation and the _-elaboration is re-checked (the
generated terms are well-formed in F*); the effect definition is lifted from DM
to F*; missing WPs are generated, and everything is sent off to the "regular"
effect checking code.

Further work on this is tracked here:
https://github.com/FStarLang/FStar/issues/753
