open Prims
let is_arith_goal (uu___ : unit) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_Derived.cur_goal () ps in
    let x1 =
      FStar_Reflection_V2_Arith.run_tm
        (FStar_Reflection_V2_Arith.is_arith_prop x) ps in
    match x1 with | FStar_Pervasives.Inr uu___1 -> true | uu___1 -> false
let rec split_arith (uu___ : unit) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = is_arith_goal () ps in
    if x
    then
      (FStarC_Tactics_V2_Builtins.prune "" ps;
       FStarC_Tactics_V2_Builtins.addns "Prims" ps;
       FStar_Tactics_V2_Derived.smt () ps)
    else
      (let x1 = FStar_Tactics_V2_Derived.cur_goal () ps in
       let x2 = FStar_Reflection_V2_Formula.term_as_formula x1 ps in
       match x2 with
       | FStar_Reflection_V2_Formula.True_ ->
           FStar_Tactics_V2_Derived.trivial () ps
       | FStar_Reflection_V2_Formula.And (l, r) ->
           FStar_Tactics_V2_Derived.seq FStar_Tactics_V2_Logic.split
             split_arith ps
       | FStar_Reflection_V2_Formula.Implies (p, q) ->
           let x3 = FStar_Tactics_V2_Logic.implies_intro () ps in
           FStar_Tactics_V2_Derived.seq split_arith
             FStar_Tactics_V2_Logic.l_revert ps
       | FStar_Reflection_V2_Formula.Forall (_x, _sort, _p) ->
           let x3 = FStar_Tactics_V2_Logic.forall_intros () ps in
           FStar_Tactics_V2_Derived.seq split_arith
             (fun uu___1 -> FStar_Tactics_V2_Logic.l_revert_all x3) ps
       | uu___1 -> ())
