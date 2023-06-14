module FStar.Tactics.V2.Coercions

open FStar.Tactics.Typeclasses

class coercible (a : Type u#aa) (b : Type u#bb) = {
  coerce : a -> b;
}

open FStar.Tactics.NamedView
open FStar.Tactics.V2.Derived

(* Move to separate module *)
instance cc_b_nv : coercible binding namedv = {
  coerce = binding_to_namedv;
}

instance cc_t_tv : coercible term Reflection.V2.Data.term_view = {
  coerce = Reflection.V2.inspect_ln
}

instance cc_tv_t : coercible Reflection.V2.Data.term_view term = {
  coerce = Reflection.V2.pack_ln
}
