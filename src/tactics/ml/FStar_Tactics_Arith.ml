open Prims
let is_arith_goal: Prims.bool FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Arith.run_tm
               (FStar_Reflection_Arith.is_arith_prop g)
       with
       | FStar_Pervasives.Inr uu____13 -> FStar_Tactics_Effect.return true
       | FStar_Pervasives.Inl s -> FStar_Tactics_Effect.return false)
let rec split_arith:
  Prims.unit ->
    (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                  Prims.l_Forall)
      FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun uu____57  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
      (fun g  ->
         FStar_Tactics_Effect.bind is_arith_goal
           (fun b  ->
              if b
              then
                FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.prune "")
                  (fun uu___87_95  ->
                     FStar_Tactics_Effect.bind
                       (FStar_Tactics_Builtins.addns "Prims")
                       (fun uu___86_97  -> FStar_Tactics_Builtins.smt))
              else
                FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
                  (fun g1  ->
                     match FStar_Reflection_Formula.term_as_formula g1 with
                     | FStar_Reflection_Formula.True_  ->
                         FStar_Tactics_Builtins.trivial
                     | FStar_Reflection_Formula.And (l,r) ->
                         FStar_Tactics_Builtins.seq FStar_Tactics_Logic.split
                           split_arith
                     | FStar_Reflection_Formula.Implies (p,q) ->
                         FStar_Tactics_Effect.bind
                           FStar_Tactics_Logic.implies_intro
                           (fun uu___88_108  ->
                              FStar_Tactics_Builtins.seq split_arith
                                FStar_Tactics_Logic.l_revert)
                     | FStar_Reflection_Formula.Forall (x,p) ->
                         FStar_Tactics_Effect.bind
                           FStar_Tactics_Logic.forall_intros
                           (fun bs  ->
                              FStar_Tactics_Builtins.seq split_arith
                                (FStar_Tactics_Logic.l_revert_all bs))
                     | uu____117 -> FStar_Tactics_Effect.return ()))) ()