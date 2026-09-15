Util:

- strengthen_comp --> label_guard
- comp_false is bogus
- 

Rel.imitate_arrow: Why split on the cases. These could be handled symmetrically

Env:

Why should Sig_effect_abbrev carry a universe list and why should Env.lookup_effect_abbrev pass in a thunk of universes?

What binders can an effect abbrev have beyond the result type?

Why can this not be: is_ghost_effect / is_tot_effect?

+  else if Const.is_gtot_lid l1 && Const.is_tot_lid l2
+       || Const.is_gtot_lid l2 && Const.is_tot_lid l1
+  then Some Const.primitive_ghost_lid

