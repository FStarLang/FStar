module Bug3185

module FT = FStar.Tactics.V2

#push-options "--print_bound_var_types --print_full_names"
// #push-options "--debug NBE"

let test_normalise (): unit =
  assert (forall (i: int). op_LessThanOrEqual == op_LessThanOrEqual)
    by (
      // the nbe step will eta expand the primops, but using units instead of ints:
      // > (fun (u1: unit) (u2: unit) -> op_LessThanOrEqual u1 u2)
      FT.norm [norm_debug; nbe];
      FT.dump "";
      // trying to intro the forall will typecheck the expression, so tactic fails
      ignore (FT.forall_intro ()))

#pop-options
