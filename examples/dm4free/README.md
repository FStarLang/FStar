Dijkstra Monads for Free
------------------------

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

Going forward:
- change the elaboration of the match to push the return _inside_ the branches
  instead of wrapping the whole branch on the outside (better for Z3)
- make the continuations example work
- fill out various TODOs in `dmff.fs` to faithfully check everything (right now,
  most checks are fairly lax);
- try out more examples
- inserting "return" on the fly when reflecting Tot computations
- extraction!

- it would be good to have a generic way of noticing that a WP
  combinator contains a branching construct within it and that it may
  lead to exponential blowup. In such a case, we should wrap the WP
  with a "name_continuation" combinator, which is currently called
  "wp_ite" and should be renamed. This is particularly important for
  the exceptions monad, where every bind contains a branch.

- dreaming: can we also generate abbreviations for the "triples" form
  of an effect?
