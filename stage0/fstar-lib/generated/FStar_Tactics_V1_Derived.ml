open Prims
let op_At :
  'uuuuu .
    unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list
  = fun uu___ -> FStar_List_Tot_Base.op_At
let (name_of_bv :
  FStarC_Reflection_Types.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    FStarC_Tactics_Unseal.unseal
      (FStarC_Reflection_V1_Builtins.inspect_bv bv).FStarC_Reflection_V1_Data.bv_ppname
let (bv_to_string :
  FStarC_Reflection_Types.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun bv -> name_of_bv bv
let (name_of_binder :
  FStarC_Reflection_Types.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> name_of_bv (FStar_Reflection_V1_Derived.bv_of_binder b)
let (binder_to_string :
  FStarC_Reflection_Types.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> bv_to_string (FStar_Reflection_V1_Derived.bv_of_binder b)
exception Goal_not_trivial 
let (uu___is_Goal_not_trivial : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Goal_not_trivial -> true | uu___ -> false
let (goals :
  unit ->
    (FStarC_Tactics_Types.goal Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = Obj.magic (FStar_Tactics_Effect.get ()) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (48)) (Prims.of_int (42)) (Prims.of_int (48))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (48)) (Prims.of_int (33)) (Prims.of_int (48))
               (Prims.of_int (50))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.goals_of uu___2))
let (smt_goals :
  unit ->
    (FStarC_Tactics_Types.goal Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = Obj.magic (FStar_Tactics_Effect.get ()) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (49)) (Prims.of_int (50)) (Prims.of_int (49))
               (Prims.of_int (58)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (49)) (Prims.of_int (37)) (Prims.of_int (49))
               (Prims.of_int (58))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.smt_goals_of uu___2))
let fail : 'a . Prims.string -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr =
  fun m ->
    FStar_Tactics_Effect.raise
      (FStarC_Tactics_Common.TacticFailure
         ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None))
let fail_silently :
  'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun m ->
    let uu___ = FStarC_Tactics_V1_Builtins.set_urgency Prims.int_zero in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (57)) (Prims.of_int (4)) (Prims.of_int (57))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (58)) (Prims.of_int (4)) (Prims.of_int (58))
               (Prims.of_int (44))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.raise
           (FStarC_Tactics_Common.TacticFailure
              ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)))
let (_cur_goal :
  unit -> (FStarC_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (62)) (Prims.of_int (10)) (Prims.of_int (62))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (62)) (Prims.of_int (4)) (Prims.of_int (64))
               (Prims.of_int (15))))) (Obj.magic uu___1)
      (fun uu___2 ->
         match uu___2 with
         | [] -> fail "no more goals"
         | g::uu___3 -> FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> g))
let (cur_env :
  unit -> (FStarC_Reflection_Types.env, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = _cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (67)) (Prims.of_int (36)) (Prims.of_int (67))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (67)) (Prims.of_int (27)) (Prims.of_int (67))
               (Prims.of_int (50))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.goal_env uu___2))
let (cur_goal :
  unit -> (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = _cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (70)) (Prims.of_int (38)) (Prims.of_int (70))
               (Prims.of_int (52)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (70)) (Prims.of_int (28)) (Prims.of_int (70))
               (Prims.of_int (52))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.goal_type uu___2))
let (cur_witness :
  unit -> (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = _cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (73)) (Prims.of_int (45)) (Prims.of_int (73))
               (Prims.of_int (59)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (73)) (Prims.of_int (32)) (Prims.of_int (73))
               (Prims.of_int (59))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.goal_witness uu___2))
let (cur_goal_safe :
  unit -> (FStarC_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = Obj.magic (FStar_Tactics_Effect.get ()) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (80)) (Prims.of_int (18)) (Prims.of_int (80))
                 (Prims.of_int (26)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (80)) (Prims.of_int (9)) (Prims.of_int (80))
                 (Prims.of_int (26))))) (Obj.magic uu___2)
        (fun uu___3 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___4 -> FStarC_Tactics_Types.goals_of uu___3)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (80)) (Prims.of_int (9)) (Prims.of_int (80))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (80)) (Prims.of_int (3)) (Prims.of_int (81))
               (Prims.of_int (16))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> match uu___2 with | g::uu___4 -> g))
let (cur_binders :
  unit ->
    (FStarC_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = cur_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (85)) (Prims.of_int (19)) (Prims.of_int (85))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (85)) (Prims.of_int (4)) (Prims.of_int (85))
               (Prims.of_int (31))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Reflection_V1_Builtins.binders_of_env uu___2))
let with_policy :
  'a .
    FStarC_Tactics_Types.guard_policy ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun pol ->
    fun f ->
      let uu___ = FStarC_Tactics_V1_Builtins.get_guard_policy () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (89)) (Prims.of_int (18)) (Prims.of_int (89))
                 (Prims.of_int (37)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (90)) (Prims.of_int (4)) (Prims.of_int (93))
                 (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun old_pol ->
              let uu___1 = FStarC_Tactics_V1_Builtins.set_guard_policy pol in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (90)) (Prims.of_int (4))
                            (Prims.of_int (90)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (90)) (Prims.of_int (25))
                            (Prims.of_int (93)) (Prims.of_int (5)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___3 = f () in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V1.Derived.fst"
                                       (Prims.of_int (91))
                                       (Prims.of_int (12))
                                       (Prims.of_int (91))
                                       (Prims.of_int (16)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V1.Derived.fst"
                                       (Prims.of_int (92)) (Prims.of_int (4))
                                       (Prims.of_int (93)) (Prims.of_int (5)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun r ->
                                    let uu___4 =
                                      FStarC_Tactics_V1_Builtins.set_guard_policy
                                        old_pol in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V1.Derived.fst"
                                                  (Prims.of_int (92))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (92))
                                                  (Prims.of_int (28)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V1.Derived.fst"
                                                  (Prims.of_int (91))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (91))
                                                  (Prims.of_int (9)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 -> r)))) uu___4)))
                        uu___2))) uu___1)
let (exact :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStarC_Tactics_Types.SMT
      (fun uu___ -> FStarC_Tactics_V1_Builtins.t_exact true false t)
let (exact_with_ref :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStarC_Tactics_Types.SMT
      (fun uu___ -> FStarC_Tactics_V1_Builtins.t_exact true true t)
let (trivial : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStarC_Tactics_V1_Builtins.norm
        [FStar_Pervasives.iota;
        FStar_Pervasives.zeta;
        FStar_Pervasives.reify_;
        FStar_Pervasives.delta;
        FStar_Pervasives.primops;
        FStar_Pervasives.simplify;
        FStar_Pervasives.unmeta] in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (107)) (Prims.of_int (2)) (Prims.of_int (107))
               (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (107)) (Prims.of_int (62)) (Prims.of_int (111))
               (Prims.of_int (31))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = cur_goal () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (108)) (Prims.of_int (10))
                          (Prims.of_int (108)) (Prims.of_int (21)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (109)) (Prims.of_int (2))
                          (Prims.of_int (111)) (Prims.of_int (31)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun g ->
                       let uu___4 =
                         FStar_Reflection_V1_Formula.term_as_formula g in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (109)) (Prims.of_int (8))
                                     (Prims.of_int (109)) (Prims.of_int (25)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (109)) (Prims.of_int (2))
                                     (Prims.of_int (111)) (Prims.of_int (31)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  match uu___5 with
                                  | FStar_Reflection_V1_Formula.True_ ->
                                      Obj.magic
                                        (Obj.repr
                                           (exact
                                              (FStarC_Reflection_V2_Builtins.pack_ln
                                                 (FStarC_Reflection_V2_Data.Tv_Const
                                                    FStarC_Reflection_V2_Data.C_Unit))))
                                  | uu___6 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.raise
                                              Goal_not_trivial))) uu___5)))
                      uu___4))) uu___2)
let (dismiss : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (123)) (Prims.of_int (10)) (Prims.of_int (123))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (123)) (Prims.of_int (4)) (Prims.of_int (125))
               (Prims.of_int (27))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | [] -> Obj.magic (Obj.repr (fail "dismiss: no more goals"))
            | uu___3::gs ->
                Obj.magic
                  (Obj.repr (FStarC_Tactics_V1_Builtins.set_goals gs)))
           uu___2)
let (flip : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (129)) (Prims.of_int (13)) (Prims.of_int (129))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (130)) (Prims.of_int (4)) (Prims.of_int (132))
               (Prims.of_int (42))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun gs ->
            let uu___2 = goals () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (130)) (Prims.of_int (10))
                          (Prims.of_int (130)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (130)) (Prims.of_int (4))
                          (Prims.of_int (132)) (Prims.of_int (42)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       match uu___3 with
                       | [] ->
                           Obj.magic
                             (Obj.repr (fail "flip: less than two goals"))
                       | uu___4::[] ->
                           Obj.magic
                             (Obj.repr (fail "flip: less than two goals"))
                       | g1::g2::gs1 ->
                           Obj.magic
                             (Obj.repr
                                (FStarC_Tactics_V1_Builtins.set_goals (g2 ::
                                   g1 :: gs1)))) uu___3))) uu___2)
let (qed : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (136)) (Prims.of_int (10)) (Prims.of_int (136))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (136)) (Prims.of_int (4)) (Prims.of_int (138))
               (Prims.of_int (32))))) (Obj.magic uu___1)
      (fun uu___2 ->
         match uu___2 with
         | [] -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ())
         | uu___3 -> fail "qed: not done!")
let (debug : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    let uu___ = FStarC_Tactics_V1_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (143)) (Prims.of_int (7)) (Prims.of_int (143))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (143)) (Prims.of_int (4)) (Prims.of_int (143))
               (Prims.of_int (32))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (FStarC_Tactics_V1_Builtins.print m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
let (smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = goals () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (150)) (Prims.of_int (10))
                 (Prims.of_int (150)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (150)) (Prims.of_int (10))
                 (Prims.of_int (150)) (Prims.of_int (32)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___4 = smt_goals () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (150)) (Prims.of_int (20))
                            (Prims.of_int (150)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (150)) (Prims.of_int (10))
                            (Prims.of_int (150)) (Prims.of_int (32)))))
                   (Obj.magic uu___4)
                   (fun uu___5 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___6 -> (uu___3, uu___5))))) uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (150)) (Prims.of_int (10)) (Prims.of_int (150))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (150)) (Prims.of_int (4)) (Prims.of_int (156))
               (Prims.of_int (11))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | ([], uu___3) ->
                Obj.magic (Obj.repr (fail "smt: no active goals"))
            | (g::gs, gs') ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 = FStarC_Tactics_V1_Builtins.set_goals gs in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (154)) (Prims.of_int (8))
                                 (Prims.of_int (154)) (Prims.of_int (20)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (155)) (Prims.of_int (8))
                                 (Prims.of_int (155)) (Prims.of_int (32)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              Obj.magic
                                (FStarC_Tactics_V1_Builtins.set_smt_goals (g
                                   :: gs'))) uu___4)))) uu___2)
let (idtac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
      uu___
let (later : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (162)) (Prims.of_int (10)) (Prims.of_int (162))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (162)) (Prims.of_int (4)) (Prims.of_int (164))
               (Prims.of_int (33))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | g::gs ->
                Obj.magic
                  (Obj.repr
                     (FStarC_Tactics_V1_Builtins.set_goals
                        ((op_At ()) gs [g])))
            | uu___3 -> Obj.magic (Obj.repr (fail "later: no goals"))) uu___2)
let (apply :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V1_Builtins.t_apply true false false t
let (apply_noinst :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V1_Builtins.t_apply true true false t
let (apply_lemma :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V1_Builtins.t_apply_lemma false false t
let (trefl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V1_Builtins.t_trefl false
let (trefl_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V1_Builtins.t_trefl true
let (commute_applied_match :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V1_Builtins.t_commute_applied_match ()
let (apply_lemma_noinst :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V1_Builtins.t_apply_lemma true false t
let (apply_lemma_rw :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V1_Builtins.t_apply_lemma false true t
let (apply_raw :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V1_Builtins.t_apply false false false t
let (exact_guard :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStarC_Tactics_Types.Goal
      (fun uu___ -> FStarC_Tactics_V1_Builtins.t_exact true false t)
let (t_pointwise :
  FStarC_Tactics_Types.direction ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun tau ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                fun uu___1 ->
                  (fun uu___1 ->
                     fun t ->
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               (true, FStarC_Tactics_Types.Continue))))
                    uu___2 uu___1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (223)) (Prims.of_int (4)) (Prims.of_int (223))
                 (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (224)) (Prims.of_int (4)) (Prims.of_int (228))
                 (Prims.of_int (24))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun ctrl ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> fun uu___3 -> tau ())) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (226)) (Prims.of_int (4))
                            (Prims.of_int (226)) (Prims.of_int (10)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (228)) (Prims.of_int (2))
                            (Prims.of_int (228)) (Prims.of_int (24)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun rw ->
                         Obj.magic
                           (FStarC_Tactics_V1_Builtins.ctrl_rewrite d ctrl rw))
                        uu___2))) uu___1)
let (topdown_rewrite :
  (FStarC_Reflection_Types.term ->
     ((Prims.bool * Prims.int), unit) FStar_Tactics_Effect.tac_repr)
    ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ctrl ->
    fun rw ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                fun t ->
                  let uu___2 = ctrl t in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V1.Derived.fst"
                             (Prims.of_int (253)) (Prims.of_int (17))
                             (Prims.of_int (253)) (Prims.of_int (23)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V1.Derived.fst"
                             (Prims.of_int (252)) (Prims.of_int (49))
                             (Prims.of_int (261)) (Prims.of_int (10)))))
                    (Obj.magic uu___2)
                    (fun uu___3 ->
                       (fun uu___3 ->
                          match uu___3 with
                          | (b, i) ->
                              let uu___4 =
                                match i with
                                | uu___5 when uu___5 = Prims.int_zero ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 ->
                                            FStarC_Tactics_Types.Continue))
                                | uu___5 when uu___5 = Prims.int_one ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 ->
                                            FStarC_Tactics_Types.Skip))
                                | uu___5 when uu___5 = (Prims.of_int (2)) ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 ->
                                            FStarC_Tactics_Types.Abort))
                                | uu___5 ->
                                    Obj.magic
                                      (fail
                                         "topdown_rewrite: bad value from ctrl") in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (255))
                                            (Prims.of_int (8))
                                            (Prims.of_int (259))
                                            (Prims.of_int (58)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (261))
                                            (Prims.of_int (6))
                                            (Prims.of_int (261))
                                            (Prims.of_int (10)))))
                                   (Obj.magic uu___4)
                                   (fun f ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> (b, f))))) uu___3))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (252)) (Prims.of_int (49))
                 (Prims.of_int (261)) (Prims.of_int (10)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (263)) (Prims.of_int (4)) (Prims.of_int (263))
                 (Prims.of_int (33))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun ctrl' ->
              Obj.magic
                (FStarC_Tactics_V1_Builtins.ctrl_rewrite
                   FStarC_Tactics_Types.TopDown ctrl' rw)) uu___1)
let (pointwise :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun tau -> t_pointwise FStarC_Tactics_Types.BottomUp tau
let (pointwise' :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun tau -> t_pointwise FStarC_Tactics_Types.TopDown tau
let (cur_module :
  unit -> (FStarC_Reflection_Types.name, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V1_Builtins.top_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (269)) (Prims.of_int (13)) (Prims.of_int (269))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (269)) (Prims.of_int (4)) (Prims.of_int (269))
               (Prims.of_int (25))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Reflection_V1_Builtins.moduleof uu___2))
let (open_modules :
  unit ->
    (FStarC_Reflection_Types.name Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V1_Builtins.top_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (272)) (Prims.of_int (21)) (Prims.of_int (272))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (272)) (Prims.of_int (4)) (Prims.of_int (272))
               (Prims.of_int (33))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 ->
              FStarC_Reflection_V1_Builtins.env_open_modules uu___2))
let (fresh_uvar :
  FStarC_Reflection_Types.typ FStar_Pervasives_Native.option ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    let uu___ = cur_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (275)) (Prims.of_int (12)) (Prims.of_int (275))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (276)) (Prims.of_int (4)) (Prims.of_int (276))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun e -> Obj.magic (FStarC_Tactics_V1_Builtins.uvar_env e o))
           uu___1)
let (unify :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (279)) (Prims.of_int (12))
                 (Prims.of_int (279)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (280)) (Prims.of_int (4)) (Prims.of_int (280))
                 (Prims.of_int (21))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e -> Obj.magic (FStarC_Tactics_V1_Builtins.unify_env e t1 t2))
             uu___1)
let (unify_guard :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (283)) (Prims.of_int (12))
                 (Prims.of_int (283)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (284)) (Prims.of_int (4)) (Prims.of_int (284))
                 (Prims.of_int (27))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              Obj.magic (FStarC_Tactics_V1_Builtins.unify_guard_env e t1 t2))
             uu___1)
let (tmatch :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (287)) (Prims.of_int (12))
                 (Prims.of_int (287)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (288)) (Prims.of_int (4)) (Prims.of_int (288))
                 (Prims.of_int (21))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e -> Obj.magic (FStarC_Tactics_V1_Builtins.match_env e t1 t2))
             uu___1)
let divide :
  'a 'b .
    Prims.int ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        (unit -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
          (('a * 'b), unit) FStar_Tactics_Effect.tac_repr
  =
  fun n ->
    fun l ->
      fun r ->
        let uu___ =
          if n < Prims.int_zero
          then Obj.magic (fail "divide: negative n")
          else
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                   (Prims.of_int (294)) (Prims.of_int (4))
                   (Prims.of_int (295)) (Prims.of_int (31)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                   (Prims.of_int (295)) (Prims.of_int (32))
                   (Prims.of_int (308)) (Prims.of_int (10)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = goals () in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V1.Derived.fst"
                             (Prims.of_int (296)) (Prims.of_int (18))
                             (Prims.of_int (296)) (Prims.of_int (26)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V1.Derived.fst"
                             (Prims.of_int (296)) (Prims.of_int (18))
                             (Prims.of_int (296)) (Prims.of_int (40)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          let uu___5 = smt_goals () in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.V1.Derived.fst"
                                        (Prims.of_int (296))
                                        (Prims.of_int (28))
                                        (Prims.of_int (296))
                                        (Prims.of_int (40)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.V1.Derived.fst"
                                        (Prims.of_int (296))
                                        (Prims.of_int (18))
                                        (Prims.of_int (296))
                                        (Prims.of_int (40)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 -> (uu___4, uu___6)))))
                         uu___4) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (296)) (Prims.of_int (18))
                              (Prims.of_int (296)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (295)) (Prims.of_int (32))
                              (Prims.of_int (308)) (Prims.of_int (10)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | (gs, sgs) ->
                               let uu___4 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         FStar_List_Tot_Base.splitAt n gs)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V1.Derived.fst"
                                             (Prims.of_int (297))
                                             (Prims.of_int (19))
                                             (Prims.of_int (297))
                                             (Prims.of_int (45)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V1.Derived.fst"
                                             (Prims.of_int (296))
                                             (Prims.of_int (43))
                                             (Prims.of_int (308))
                                             (Prims.of_int (10)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | (gs1, gs2) ->
                                              let uu___6 =
                                                FStarC_Tactics_V1_Builtins.set_goals
                                                  gs1 in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.V1.Derived.fst"
                                                            (Prims.of_int (299))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (299))
                                                            (Prims.of_int (17)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.V1.Derived.fst"
                                                            (Prims.of_int (299))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (308))
                                                            (Prims.of_int (10)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      (fun uu___7 ->
                                                         let uu___8 =
                                                           FStarC_Tactics_V1_Builtins.set_smt_goals
                                                             [] in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 (fun uu___9
                                                                    ->
                                                                    let uu___10
                                                                    = l () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    goals () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    smt_goals
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (uu___13,
                                                                    uu___15)))))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (gsl,
                                                                    sgsl) ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.set_goals
                                                                    gs2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.set_smt_goals
                                                                    [] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    = r () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun y ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    goals () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    smt_goals
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (uu___20,
                                                                    uu___22)))))
                                                                    uu___20) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (gsr,
                                                                    sgsr) ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.set_goals
                                                                    ((op_At
                                                                    ()) gsl
                                                                    gsr) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.set_smt_goals
                                                                    ((op_At
                                                                    ()) sgs
                                                                    ((op_At
                                                                    ()) sgsl
                                                                    sgsr)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    -> (x, y)))))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                   uu___9)))
                                                        uu___7))) uu___5)))
                          uu___3))) uu___1)
let rec (iseq :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun ts ->
       match ts with
       | t::ts1 ->
           Obj.magic
             (Obj.repr
                (let uu___ = divide Prims.int_one t (fun uu___1 -> iseq ts1) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (312)) (Prims.of_int (23))
                            (Prims.of_int (312)) (Prims.of_int (53)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (312)) (Prims.of_int (57))
                            (Prims.of_int (312)) (Prims.of_int (59)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))))
      uu___
let focus :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (318)) (Prims.of_int (10)) (Prims.of_int (318))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (318)) (Prims.of_int (4)) (Prims.of_int (325))
               (Prims.of_int (9))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (Obj.repr (fail "focus: no goals"))
            | g::gs ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = smt_goals () in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (321)) (Prims.of_int (18))
                                 (Prims.of_int (321)) (Prims.of_int (30)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (322)) (Prims.of_int (8))
                                 (Prims.of_int (325)) (Prims.of_int (9)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun sgs ->
                              let uu___3 =
                                FStarC_Tactics_V1_Builtins.set_goals [g] in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (322))
                                            (Prims.of_int (8))
                                            (Prims.of_int (322))
                                            (Prims.of_int (21)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (322))
                                            (Prims.of_int (23))
                                            (Prims.of_int (325))
                                            (Prims.of_int (9)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         let uu___5 =
                                           FStarC_Tactics_V1_Builtins.set_smt_goals
                                             [] in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V1.Derived.fst"
                                                       (Prims.of_int (322))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (322))
                                                       (Prims.of_int (39)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V1.Derived.fst"
                                                       (Prims.of_int (322))
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (325))
                                                       (Prims.of_int (9)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun uu___6 ->
                                                    let uu___7 = t () in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V1.Derived.fst"
                                                                  (Prims.of_int (323))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (323))
                                                                  (Prims.of_int (20)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V1.Derived.fst"
                                                                  (Prims.of_int (324))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (325))
                                                                  (Prims.of_int (9)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            (fun x ->
                                                               let uu___8 =
                                                                 let uu___9 =
                                                                   let uu___10
                                                                    =
                                                                    goals () in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (op_At ())
                                                                    uu___11
                                                                    gs)) in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (33)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (33)))))
                                                                   (Obj.magic
                                                                    uu___9)
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.set_goals
                                                                    uu___10))
                                                                    uu___10) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (9)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    smt_goals
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (op_At ())
                                                                    uu___13
                                                                    sgs)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.set_smt_goals
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> x))))
                                                                    uu___9)))
                                                              uu___8)))
                                                   uu___6))) uu___4))) uu___3))))
           uu___1)
let (dump1 : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m -> focus (fun uu___ -> FStarC_Tactics_V1_Builtins.dump m)
let rec mapAll :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (331)) (Prims.of_int (10)) (Prims.of_int (331))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (331)) (Prims.of_int (4)) (Prims.of_int (333))
               (Prims.of_int (66))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> [])))
            | uu___2::uu___3 ->
                Obj.magic
                  (Obj.repr
                     (let uu___4 =
                        divide Prims.int_one t (fun uu___5 -> mapAll t) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (333)) (Prims.of_int (27))
                                 (Prims.of_int (333)) (Prims.of_int (58)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (333)) (Prims.of_int (13))
                                 (Prims.of_int (333)) (Prims.of_int (66)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 ->
                                match uu___5 with | (h, t1) -> h :: t1)))))
           uu___1)
let rec (iterAll :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (337)) (Prims.of_int (10)) (Prims.of_int (337))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (337)) (Prims.of_int (4)) (Prims.of_int (339))
               (Prims.of_int (60))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())))
            | uu___2::uu___3 ->
                Obj.magic
                  (Obj.repr
                     (let uu___4 =
                        divide Prims.int_one t (fun uu___5 -> iterAll t) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (339)) (Prims.of_int (22))
                                 (Prims.of_int (339)) (Prims.of_int (54)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (339)) (Prims.of_int (58))
                                 (Prims.of_int (339)) (Prims.of_int (60)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 -> ()))))) uu___1)
let (iterAllSMT :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      let uu___1 = goals () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (342)) (Prims.of_int (18))
                 (Prims.of_int (342)) (Prims.of_int (26)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (342)) (Prims.of_int (18))
                 (Prims.of_int (342)) (Prims.of_int (40)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___3 = smt_goals () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (342)) (Prims.of_int (28))
                            (Prims.of_int (342)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (342)) (Prims.of_int (18))
                            (Prims.of_int (342)) (Prims.of_int (40)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> (uu___2, uu___4))))) uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (342)) (Prims.of_int (18)) (Prims.of_int (342))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (341)) (Prims.of_int (50)) (Prims.of_int (348))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (gs, sgs) ->
                let uu___2 = FStarC_Tactics_V1_Builtins.set_goals sgs in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (343)) (Prims.of_int (4))
                              (Prims.of_int (343)) (Prims.of_int (17)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (344)) (Prims.of_int (4))
                              (Prims.of_int (348)) (Prims.of_int (28)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 =
                             FStarC_Tactics_V1_Builtins.set_smt_goals [] in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V1.Derived.fst"
                                         (Prims.of_int (344))
                                         (Prims.of_int (4))
                                         (Prims.of_int (344))
                                         (Prims.of_int (20)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V1.Derived.fst"
                                         (Prims.of_int (345))
                                         (Prims.of_int (4))
                                         (Prims.of_int (348))
                                         (Prims.of_int (28)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      let uu___6 = iterAll t in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V1.Derived.fst"
                                                    (Prims.of_int (345))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (345))
                                                    (Prims.of_int (13)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V1.Derived.fst"
                                                    (Prims.of_int (345))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (348))
                                                    (Prims.of_int (28)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              (fun uu___7 ->
                                                 let uu___8 =
                                                   let uu___9 = goals () in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V1.Derived.fst"
                                                              (Prims.of_int (346))
                                                              (Prims.of_int (20))
                                                              (Prims.of_int (346))
                                                              (Prims.of_int (28)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V1.Derived.fst"
                                                              (Prims.of_int (346))
                                                              (Prims.of_int (20))
                                                              (Prims.of_int (346))
                                                              (Prims.of_int (42)))))
                                                     (Obj.magic uu___9)
                                                     (fun uu___10 ->
                                                        (fun uu___10 ->
                                                           let uu___11 =
                                                             smt_goals () in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (42)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (42)))))
                                                                (Obj.magic
                                                                   uu___11)
                                                                (fun uu___12
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (uu___10,
                                                                    uu___12)))))
                                                          uu___10) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V1.Derived.fst"
                                                               (Prims.of_int (346))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (346))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V1.Derived.fst"
                                                               (Prims.of_int (345))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (348))
                                                               (Prims.of_int (28)))))
                                                      (Obj.magic uu___8)
                                                      (fun uu___9 ->
                                                         (fun uu___9 ->
                                                            match uu___9 with
                                                            | (gs', sgs') ->
                                                                let uu___10 =
                                                                  FStarC_Tactics_V1_Builtins.set_goals
                                                                    gs in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.set_smt_goals
                                                                    ((op_At
                                                                    ()) gs'
                                                                    sgs')))
                                                                    uu___11)))
                                                           uu___9))) uu___7)))
                                     uu___5))) uu___3))) uu___1)
let (seq :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      focus
        (fun uu___ ->
           let uu___1 = f () in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                      (Prims.of_int (354)) (Prims.of_int (21))
                      (Prims.of_int (354)) (Prims.of_int (25)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                      (Prims.of_int (354)) (Prims.of_int (27))
                      (Prims.of_int (354)) (Prims.of_int (36)))))
             (Obj.magic uu___1)
             (fun uu___2 -> (fun uu___2 -> Obj.magic (iterAll g)) uu___2))
let (exact_args :
  FStarC_Reflection_V1_Data.aqualv Prims.list ->
    FStarC_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun qs ->
    fun t ->
      focus
        (fun uu___ ->
           let uu___1 =
             Obj.magic
               (FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 -> FStar_List_Tot_Base.length qs)) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                      (Prims.of_int (358)) (Prims.of_int (16))
                      (Prims.of_int (358)) (Prims.of_int (39)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                      (Prims.of_int (358)) (Prims.of_int (42))
                      (Prims.of_int (364)) (Prims.of_int (44)))))
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun n ->
                   let uu___2 =
                     FStar_Tactics_Util.repeatn n
                       (fun uu___3 -> fresh_uvar FStar_Pervasives_Native.None) in
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (359)) (Prims.of_int (18))
                                 (Prims.of_int (359)) (Prims.of_int (55)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (359)) (Prims.of_int (58))
                                 (Prims.of_int (364)) (Prims.of_int (44)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uvs ->
                              let uu___3 =
                                let uu___4 = FStar_Tactics_Util.zip uvs qs in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (360))
                                           (Prims.of_int (26))
                                           (Prims.of_int (360))
                                           (Prims.of_int (38)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (360))
                                           (Prims.of_int (17))
                                           (Prims.of_int (360))
                                           (Prims.of_int (38)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___6 ->
                                          FStar_Reflection_V1_Derived.mk_app
                                            t uu___5)) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (360))
                                            (Prims.of_int (17))
                                            (Prims.of_int (360))
                                            (Prims.of_int (38)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (361))
                                            (Prims.of_int (8))
                                            (Prims.of_int (364))
                                            (Prims.of_int (44)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun t' ->
                                         let uu___4 = exact t' in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V1.Derived.fst"
                                                       (Prims.of_int (361))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (361))
                                                       (Prims.of_int (16)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V1.Derived.fst"
                                                       (Prims.of_int (362))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (364))
                                                       (Prims.of_int (44)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun uu___5 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Util.iter
                                                         (fun uu___6 ->
                                                            (fun uv ->
                                                               if
                                                                 FStar_Reflection_V1_Derived.is_uvar
                                                                   uv
                                                               then
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStarC_Tactics_V1_Builtins.unshelve
                                                                    uv))
                                                               else
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                              uu___6)
                                                         (FStar_List_Tot_Base.rev
                                                            uvs))) uu___5)))
                                        uu___4))) uu___3))) uu___2))
let (exact_n :
  Prims.int ->
    FStarC_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun n ->
    fun t ->
      let uu___ =
        FStar_Tactics_Util.repeatn n
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> FStarC_Reflection_V1_Data.Q_Explicit)))
               uu___1) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (368)) (Prims.of_int (15))
                 (Prims.of_int (368)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (368)) (Prims.of_int (4)) (Prims.of_int (368))
                 (Prims.of_int (51))))) (Obj.magic uu___)
        (fun uu___1 -> (fun uu___1 -> Obj.magic (exact_args uu___1 t)) uu___1)
let (ngoals : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (371)) (Prims.of_int (47)) (Prims.of_int (371))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (371)) (Prims.of_int (26)) (Prims.of_int (371))
               (Prims.of_int (57))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStar_List_Tot_Base.length uu___2))
let (ngoals_smt : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = smt_goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (374)) (Prims.of_int (51)) (Prims.of_int (374))
               (Prims.of_int (65)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (374)) (Prims.of_int (30)) (Prims.of_int (374))
               (Prims.of_int (65))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStar_List_Tot_Base.length uu___2))
let (fresh_bv :
  unit -> (FStarC_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V1_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (382)) (Prims.of_int (12)) (Prims.of_int (382))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (383)) (Prims.of_int (4)) (Prims.of_int (383))
               (Prims.of_int (42))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun i ->
            Obj.magic
              (FStarC_Tactics_V1_Builtins.fresh_bv_named
                 (Prims.strcat "x" (Prims.string_of_int i)))) uu___2)
let (fresh_binder_named :
  Prims.string ->
    FStarC_Reflection_Types.typ ->
      (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      let uu___ = FStarC_Tactics_V1_Builtins.fresh_bv_named nm in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (386)) (Prims.of_int (14))
                 (Prims.of_int (386)) (Prims.of_int (33)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (386)) (Prims.of_int (4)) (Prims.of_int (386))
                 (Prims.of_int (35))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 -> FStar_Reflection_V1_Derived.mk_binder uu___1 t))
let (fresh_binder :
  FStarC_Reflection_Types.typ ->
    (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (390)) (Prims.of_int (12)) (Prims.of_int (390))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (391)) (Prims.of_int (4)) (Prims.of_int (391))
               (Prims.of_int (48))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun i ->
            Obj.magic
              (fresh_binder_named (Prims.strcat "x" (Prims.string_of_int i))
                 t)) uu___1)
let (fresh_implicit_binder_named :
  Prims.string ->
    FStarC_Reflection_Types.typ ->
      (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      let uu___ = FStarC_Tactics_V1_Builtins.fresh_bv_named nm in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (394)) (Prims.of_int (23))
                 (Prims.of_int (394)) (Prims.of_int (42)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (394)) (Prims.of_int (4)) (Prims.of_int (394))
                 (Prims.of_int (44))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                FStar_Reflection_V1_Derived.mk_implicit_binder uu___1 t))
let (fresh_implicit_binder :
  FStarC_Reflection_Types.typ ->
    (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (398)) (Prims.of_int (12)) (Prims.of_int (398))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (399)) (Prims.of_int (4)) (Prims.of_int (399))
               (Prims.of_int (57))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun i ->
            Obj.magic
              (fresh_implicit_binder_named
                 (Prims.strcat "x" (Prims.string_of_int i)) t)) uu___1)
let (guard : Prims.bool -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun b ->
       if Prims.op_Negation b
       then Obj.magic (fail "guard failed")
       else Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
      uu___
let try_with :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (Prims.exn -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun h ->
      let uu___ = FStarC_Tactics_V1_Builtins.catch f in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (412)) (Prims.of_int (10))
                 (Prims.of_int (412)) (Prims.of_int (17)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (412)) (Prims.of_int (4)) (Prims.of_int (414))
                 (Prims.of_int (16))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives.Inl e -> Obj.magic (Obj.repr (h e))
              | FStar_Pervasives.Inr x ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> x))))
             uu___1)
let trytac :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a FStar_Pervasives_Native.option, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    try_with
      (fun uu___ ->
         match () with
         | () ->
             let uu___1 = t () in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                        (Prims.of_int (417)) (Prims.of_int (13))
                        (Prims.of_int (417)) (Prims.of_int (19)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                        (Prims.of_int (417)) (Prims.of_int (8))
                        (Prims.of_int (417)) (Prims.of_int (19)))))
               (Obj.magic uu___1)
               (fun uu___2 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___3 -> FStar_Pervasives_Native.Some uu___2)))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> FStar_Pervasives_Native.None))) uu___)
let or_else :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t1 ->
    fun t2 ->
      try_with (fun uu___ -> match () with | () -> t1 ())
        (fun uu___ -> t2 ())
let op_Less_Bar_Greater :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        unit -> ('a, unit) FStar_Tactics_Effect.tac_repr
  = fun t1 -> fun t2 -> fun uu___ -> or_else t1 t2
let first :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) Prims.list ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun ts ->
    FStar_List_Tot_Base.fold_right op_Less_Bar_Greater ts
      (fun uu___ -> (fun uu___ -> Obj.magic (fail "no tactics to try")) uu___)
      ()
let rec repeat :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.catch t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (434)) (Prims.of_int (10)) (Prims.of_int (434))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (434)) (Prims.of_int (4)) (Prims.of_int (436))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Pervasives.Inl uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> [])))
            | FStar_Pervasives.Inr x ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = repeat t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (436)) (Prims.of_int (20))
                                 (Prims.of_int (436)) (Prims.of_int (28)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (436)) (Prims.of_int (15))
                                 (Prims.of_int (436)) (Prims.of_int (28)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> x :: uu___3))))) uu___1)
let repeat1 :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    let uu___ = t () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (439)) (Prims.of_int (4)) (Prims.of_int (439))
               (Prims.of_int (8)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (439)) (Prims.of_int (4)) (Prims.of_int (439))
               (Prims.of_int (20))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = repeat t in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (439)) (Prims.of_int (12))
                          (Prims.of_int (439)) (Prims.of_int (20)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (439)) (Prims.of_int (4))
                          (Prims.of_int (439)) (Prims.of_int (20)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 -> uu___1 :: uu___3)))) uu___1)
let repeat' :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    let uu___ = repeat f in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (442)) (Prims.of_int (12)) (Prims.of_int (442))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (442)) (Prims.of_int (24)) (Prims.of_int (442))
               (Prims.of_int (26))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (norm_term :
  FStar_Pervasives.norm_step Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      let uu___ =
        try_with (fun uu___1 -> match () with | () -> cur_env ())
          (fun uu___1 -> FStarC_Tactics_V1_Builtins.top_env ()) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (446)) (Prims.of_int (8)) (Prims.of_int (447))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (449)) (Prims.of_int (4)) (Prims.of_int (449))
                 (Prims.of_int (23))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              Obj.magic (FStarC_Tactics_V1_Builtins.norm_term_env e s t))
             uu___1)
let (join_all_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      let uu___2 = goals () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (456)) (Prims.of_int (16))
                 (Prims.of_int (456)) (Prims.of_int (24)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (456)) (Prims.of_int (16))
                 (Prims.of_int (456)) (Prims.of_int (38)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___4 = smt_goals () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (456)) (Prims.of_int (26))
                            (Prims.of_int (456)) (Prims.of_int (38)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (456)) (Prims.of_int (16))
                            (Prims.of_int (456)) (Prims.of_int (38)))))
                   (Obj.magic uu___4)
                   (fun uu___5 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___6 -> (uu___3, uu___5))))) uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (456)) (Prims.of_int (16)) (Prims.of_int (456))
               (Prims.of_int (38)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (455)) (Prims.of_int (27)) (Prims.of_int (462))
               (Prims.of_int (20))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | (gs, sgs) ->
                let uu___3 = FStarC_Tactics_V1_Builtins.set_smt_goals [] in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (457)) (Prims.of_int (2))
                              (Prims.of_int (457)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (458)) (Prims.of_int (2))
                              (Prims.of_int (462)) (Prims.of_int (20)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           let uu___5 =
                             FStarC_Tactics_V1_Builtins.set_goals sgs in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V1.Derived.fst"
                                         (Prims.of_int (458))
                                         (Prims.of_int (2))
                                         (Prims.of_int (458))
                                         (Prims.of_int (15)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V1.Derived.fst"
                                         (Prims.of_int (459))
                                         (Prims.of_int (2))
                                         (Prims.of_int (462))
                                         (Prims.of_int (20)))))
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun uu___6 ->
                                      let uu___7 =
                                        repeat'
                                          FStarC_Tactics_V1_Builtins.join in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V1.Derived.fst"
                                                    (Prims.of_int (459))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (459))
                                                    (Prims.of_int (14)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V1.Derived.fst"
                                                    (Prims.of_int (459))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (462))
                                                    (Prims.of_int (20)))))
                                           (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              (fun uu___8 ->
                                                 let uu___9 = goals () in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V1.Derived.fst"
                                                               (Prims.of_int (460))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (460))
                                                               (Prims.of_int (21)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V1.Derived.fst"
                                                               (Prims.of_int (461))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (462))
                                                               (Prims.of_int (20)))))
                                                      (Obj.magic uu___9)
                                                      (fun uu___10 ->
                                                         (fun sgs' ->
                                                            let uu___10 =
                                                              FStarC_Tactics_V1_Builtins.set_goals
                                                                gs in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (461))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (461))
                                                                    (Prims.of_int (14)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (20)))))
                                                                 (Obj.magic
                                                                    uu___10)
                                                                 (fun uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.set_smt_goals
                                                                    sgs'))
                                                                    uu___11)))
                                                           uu___10))) uu___8)))
                                     uu___6))) uu___4))) uu___2)
let discard :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun tau ->
    fun uu___ ->
      let uu___1 = tau () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (465)) (Prims.of_int (22))
                 (Prims.of_int (465)) (Prims.of_int (28)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (465)) (Prims.of_int (32))
                 (Prims.of_int (465)) (Prims.of_int (34)))))
        (Obj.magic uu___1)
        (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let rec repeatseq :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    let uu___ =
      trytac
        (fun uu___1 -> seq (discard t) (discard (fun uu___2 -> repeatseq t))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (469)) (Prims.of_int (12)) (Prims.of_int (469))
               (Prims.of_int (82)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (469)) (Prims.of_int (86)) (Prims.of_int (469))
               (Prims.of_int (88))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (tadmit : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V1_Builtins.tadmit_t
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_Unit))
let (admit1 : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> tadmit ()
let (admit_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = repeat tadmit in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (477)) (Prims.of_int (12)) (Prims.of_int (477))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (478)) (Prims.of_int (4)) (Prims.of_int (478))
               (Prims.of_int (6))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let (is_guard : unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = _cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (482)) (Prims.of_int (33)) (Prims.of_int (482))
               (Prims.of_int (47)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (482)) (Prims.of_int (4)) (Prims.of_int (482))
               (Prims.of_int (47))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.is_guard uu___2))
let (skip_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = is_guard () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (485)) (Prims.of_int (7)) (Prims.of_int (485))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (485)) (Prims.of_int (4)) (Prims.of_int (487))
               (Prims.of_int (16))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            if uu___2
            then Obj.magic (Obj.repr (smt ()))
            else Obj.magic (Obj.repr (fail ""))) uu___2)
let (guards_to_smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = repeat skip_guard in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (490)) (Prims.of_int (12)) (Prims.of_int (490))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (491)) (Prims.of_int (4)) (Prims.of_int (491))
               (Prims.of_int (6))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let (simpl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V1_Builtins.norm
      [FStar_Pervasives.simplify; FStar_Pervasives.primops]
let (whnf : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V1_Builtins.norm
      [FStar_Pervasives.weak;
      FStar_Pervasives.hnf;
      FStar_Pervasives.primops;
      FStar_Pervasives.delta]
let (compute : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V1_Builtins.norm
      [FStar_Pervasives.primops;
      FStar_Pervasives.iota;
      FStar_Pervasives.delta;
      FStar_Pervasives.zeta]
let (intros :
  unit ->
    (FStarC_Reflection_Types.binder Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> repeat FStarC_Tactics_V1_Builtins.intro
let (intros' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = intros () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (499)) (Prims.of_int (36)) (Prims.of_int (499))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (499)) (Prims.of_int (49)) (Prims.of_int (499))
               (Prims.of_int (51))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let (destruct :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = FStarC_Tactics_V1_Builtins.t_destruct tm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (500)) (Prims.of_int (37)) (Prims.of_int (500))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (500)) (Prims.of_int (54)) (Prims.of_int (500))
               (Prims.of_int (56))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (destruct_intros :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    seq
      (fun uu___ ->
         let uu___1 = FStarC_Tactics_V1_Builtins.t_destruct tm in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                    (Prims.of_int (501)) (Prims.of_int (59))
                    (Prims.of_int (501)) (Prims.of_int (72)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                    (Prims.of_int (501)) (Prims.of_int (76))
                    (Prims.of_int (501)) (Prims.of_int (78)))))
           (Obj.magic uu___1)
           (fun uu___2 ->
              FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))) intros'
let __cut : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
let (tcut :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (507)) (Prims.of_int (12)) (Prims.of_int (507))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (507)) (Prims.of_int (26)) (Prims.of_int (510))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun g ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_Reflection_V1_Derived.mk_e_app
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "V1";
                                 "Derived";
                                 "__cut"]))) [t; g])) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (508)) (Prims.of_int (13))
                          (Prims.of_int (508)) (Prims.of_int (37)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (509)) (Prims.of_int (4))
                          (Prims.of_int (510)) (Prims.of_int (12)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun tt ->
                       let uu___2 = apply tt in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (509)) (Prims.of_int (4))
                                     (Prims.of_int (509)) (Prims.of_int (12)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (510)) (Prims.of_int (4))
                                     (Prims.of_int (510)) (Prims.of_int (12)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  Obj.magic
                                    (FStarC_Tactics_V1_Builtins.intro ()))
                                 uu___3))) uu___2))) uu___1)
let (pose :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      apply
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "V1"; "Derived"; "__cut"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (513)) (Prims.of_int (4)) (Prims.of_int (513))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (514)) (Prims.of_int (4)) (Prims.of_int (516))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = flip () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (514)) (Prims.of_int (4))
                          (Prims.of_int (514)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (515)) (Prims.of_int (4))
                          (Prims.of_int (516)) (Prims.of_int (12)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 = exact t in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (515)) (Prims.of_int (4))
                                     (Prims.of_int (515)) (Prims.of_int (11)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (516)) (Prims.of_int (4))
                                     (Prims.of_int (516)) (Prims.of_int (12)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  Obj.magic
                                    (FStarC_Tactics_V1_Builtins.intro ()))
                                 uu___5))) uu___3))) uu___1)
let (intro_as :
  Prims.string ->
    (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    let uu___ = FStarC_Tactics_V1_Builtins.intro () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (519)) (Prims.of_int (12)) (Prims.of_int (519))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (520)) (Prims.of_int (4)) (Prims.of_int (520))
               (Prims.of_int (17))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b -> Obj.magic (FStarC_Tactics_V1_Builtins.rename_to b s))
           uu___1)
let (pose_as :
  Prims.string ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      let uu___ = pose t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (523)) (Prims.of_int (12))
                 (Prims.of_int (523)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (524)) (Prims.of_int (4)) (Prims.of_int (524))
                 (Prims.of_int (17))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun b -> Obj.magic (FStarC_Tactics_V1_Builtins.rename_to b s))
             uu___1)
let for_each_binder :
  'a .
    (FStarC_Reflection_Types.binder ->
       ('a, unit) FStar_Tactics_Effect.tac_repr)
      -> ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    let uu___ = cur_binders () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (527)) (Prims.of_int (10)) (Prims.of_int (527))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (527)) (Prims.of_int (4)) (Prims.of_int (527))
               (Prims.of_int (26))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_Util.map f uu___1)) uu___1)
let rec (revert_all :
  FStarC_Reflection_Types.binders ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
       | uu___::tl ->
           Obj.magic
             (Obj.repr
                (let uu___1 = FStarC_Tactics_V1_Builtins.revert () in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (532)) (Prims.of_int (15))
                            (Prims.of_int (532)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (533)) (Prims.of_int (15))
                            (Prims.of_int (533)) (Prims.of_int (28)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 -> Obj.magic (revert_all tl)) uu___2))))
      uu___
let (bv_to_term :
  FStarC_Reflection_Types.bv ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    FStarC_Tactics_V1_Builtins.pack (FStarC_Reflection_V1_Data.Tv_Var bv)
let (binder_to_term :
  FStarC_Reflection_Types.binder ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V1_Builtins.inspect_binder b)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (540)) (Prims.of_int (14)) (Prims.of_int (540))
               (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (541)) (Prims.of_int (2)) (Prims.of_int (541))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun bview ->
            Obj.magic (bv_to_term bview.FStarC_Reflection_V1_Data.binder_bv))
           uu___1)
let (binder_sort :
  FStarC_Reflection_Types.binder ->
    (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun b ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               (FStarC_Reflection_V1_Builtins.inspect_binder b).FStarC_Reflection_V1_Data.binder_sort)))
      uu___
let rec (__assumption_aux :
  FStarC_Reflection_Types.binders ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] -> Obj.magic (Obj.repr (fail "no assumption matches goal"))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (let uu___ = binder_to_term b in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (553)) (Prims.of_int (16))
                            (Prims.of_int (553)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (554)) (Prims.of_int (8))
                            (Prims.of_int (557)) (Prims.of_int (27)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun t ->
                         Obj.magic
                           (try_with
                              (fun uu___1 -> match () with | () -> exact t)
                              (fun uu___1 ->
                                 try_with
                                   (fun uu___2 ->
                                      match () with
                                      | () ->
                                          let uu___3 =
                                            apply
                                              (FStarC_Reflection_V2_Builtins.pack_ln
                                                 (FStarC_Reflection_V2_Data.Tv_FVar
                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                       ["FStar";
                                                       "Squash";
                                                       "return_squash"]))) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V1.Derived.fst"
                                                     (Prims.of_int (555))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (555))
                                                     (Prims.of_int (48)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V1.Derived.fst"
                                                     (Prims.of_int (556))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (556))
                                                     (Prims.of_int (20)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  Obj.magic (exact t)) uu___4))
                                   (fun uu___2 -> __assumption_aux bs1))))
                        uu___1)))) uu___
let (assumption : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = cur_binders () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (560)) (Prims.of_int (21)) (Prims.of_int (560))
               (Prims.of_int (37)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (560)) (Prims.of_int (4)) (Prims.of_int (560))
               (Prims.of_int (37))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (__assumption_aux uu___2)) uu___2)
let (destruct_equality_implication :
  FStarC_Reflection_Types.term ->
    ((FStar_Reflection_V1_Formula.formula * FStarC_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Reflection_V1_Formula.term_as_formula t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (563)) (Prims.of_int (10)) (Prims.of_int (563))
               (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (563)) (Prims.of_int (4)) (Prims.of_int (570))
               (Prims.of_int (15))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V1_Formula.Implies (lhs, rhs) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        FStar_Reflection_V1_Formula.term_as_formula' lhs in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (565)) (Prims.of_int (18))
                                 (Prims.of_int (565)) (Prims.of_int (38)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (566)) (Prims.of_int (14))
                                 (Prims.of_int (568)) (Prims.of_int (19)))))
                        (Obj.magic uu___2)
                        (fun lhs1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                match lhs1 with
                                | FStar_Reflection_V1_Formula.Comp
                                    (FStar_Reflection_V1_Formula.Eq uu___4,
                                     uu___5, uu___6)
                                    ->
                                    FStar_Pervasives_Native.Some (lhs1, rhs)
                                | uu___4 -> FStar_Pervasives_Native.None))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> FStar_Pervasives_Native.None))))
           uu___1)
let (rewrite' :
  FStarC_Reflection_Types.binder ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    op_Less_Bar_Greater
      (op_Less_Bar_Greater
         (fun uu___ -> FStarC_Tactics_V1_Builtins.rewrite b)
         (fun uu___ ->
            let uu___1 = FStarC_Tactics_V1_Builtins.binder_retype b in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                       (Prims.of_int (579)) (Prims.of_int (20))
                       (Prims.of_int (579)) (Prims.of_int (35)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                       (Prims.of_int (580)) (Prims.of_int (20))
                       (Prims.of_int (581)) (Prims.of_int (29)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___3 =
                      apply_lemma
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "V1";
                                 "Derived";
                                 "__eq_sym"]))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V1.Derived.fst"
                                  (Prims.of_int (580)) (Prims.of_int (20))
                                  (Prims.of_int (580)) (Prims.of_int (43)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V1.Derived.fst"
                                  (Prims.of_int (581)) (Prims.of_int (20))
                                  (Prims.of_int (581)) (Prims.of_int (29)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun uu___4 ->
                               Obj.magic
                                 (FStarC_Tactics_V1_Builtins.rewrite b))
                              uu___4))) uu___2)))
      (fun uu___ -> (fun uu___ -> Obj.magic (fail "rewrite' failed")) uu___)
      ()
let rec (try_rewrite_equality :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.binders ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun x ->
         fun bs ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
           | x_t::bs1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       FStar_Reflection_V1_Formula.term_as_formula
                         (FStar_Reflection_V1_Derived.type_of_binder x_t) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.Derived.fst"
                                (Prims.of_int (589)) (Prims.of_int (20))
                                (Prims.of_int (589)) (Prims.of_int (56)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.Derived.fst"
                                (Prims.of_int (589)) (Prims.of_int (14))
                                (Prims.of_int (595)) (Prims.of_int (37)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | FStar_Reflection_V1_Formula.Comp
                                 (FStar_Reflection_V1_Formula.Eq uu___2, y,
                                  uu___3)
                                 ->
                                 if FStarC_Reflection_V1_Builtins.term_eq x y
                                 then
                                   Obj.magic
                                     (FStarC_Tactics_V1_Builtins.rewrite x_t)
                                 else Obj.magic (try_rewrite_equality x bs1)
                             | uu___2 ->
                                 Obj.magic (try_rewrite_equality x bs1))
                            uu___1)))) uu___1 uu___
let rec (rewrite_all_context_equalities :
  FStarC_Reflection_Types.binders ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
       | x_t::bs1 ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   try_with
                     (fun uu___1 ->
                        match () with
                        | () -> FStarC_Tactics_V1_Builtins.rewrite x_t)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> ()))) uu___1) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (602)) (Prims.of_int (8))
                            (Prims.of_int (602)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (603)) (Prims.of_int (8))
                            (Prims.of_int (603)) (Prims.of_int (41)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic (rewrite_all_context_equalities bs1))
                        uu___1)))) uu___
let (rewrite_eqs_from_context :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = cur_binders () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (607)) (Prims.of_int (35)) (Prims.of_int (607))
               (Prims.of_int (51)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (607)) (Prims.of_int (4)) (Prims.of_int (607))
               (Prims.of_int (51))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (rewrite_all_context_equalities uu___2))
           uu___2)
let (rewrite_equality :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = cur_binders () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (610)) (Prims.of_int (27)) (Prims.of_int (610))
               (Prims.of_int (43)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (610)) (Prims.of_int (4)) (Prims.of_int (610))
               (Prims.of_int (43))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (try_rewrite_equality t uu___1)) uu___1)
let (unfold_def :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (613)) (Prims.of_int (10)) (Prims.of_int (613))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (613)) (Prims.of_int (4)) (Prims.of_int (617))
               (Prims.of_int (46))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStarC_Reflection_V1_Data.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                FStarC_Reflection_V1_Builtins.implode_qn
                                  (FStarC_Reflection_V1_Builtins.inspect_fv
                                     fv))) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (615)) (Prims.of_int (16))
                                 (Prims.of_int (615)) (Prims.of_int (42)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (616)) (Prims.of_int (8))
                                 (Prims.of_int (616)) (Prims.of_int (30)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun n ->
                              Obj.magic
                                (FStarC_Tactics_V1_Builtins.norm
                                   [FStar_Pervasives.delta_fully [n]]))
                             uu___3)))
            | uu___2 ->
                Obj.magic (Obj.repr (fail "unfold_def: term is not a fv")))
           uu___1)
let (l_to_r :
  FStarC_Reflection_Types.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lems ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_Util.fold_left
                    (fun uu___5 ->
                       fun uu___4 ->
                         (fun k ->
                            fun l ->
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___4 ->
                                      fun uu___5 ->
                                        or_else
                                          (fun uu___6 -> apply_lemma_rw l) k)))
                           uu___5 uu___4) trefl lems in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                           (Prims.of_int (624)) (Prims.of_int (8))
                           (Prims.of_int (627)) (Prims.of_int (31)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                           (Prims.of_int (624)) (Prims.of_int (8))
                           (Prims.of_int (627)) (Prims.of_int (31)))))
                  (Obj.magic uu___3)
                  (fun uu___4 -> (fun uu___4 -> Obj.magic (uu___4 ())) uu___4))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (624)) (Prims.of_int (8)) (Prims.of_int (627))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (628)) (Prims.of_int (4)) (Prims.of_int (628))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun first_or_trefl -> Obj.magic (pointwise first_or_trefl)) uu___1)
let (mk_squash :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term) =
  fun t ->
    let sq =
      FStarC_Reflection_V1_Builtins.pack_ln
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.squash_qn)) in
    FStar_Reflection_V1_Derived.mk_e_app sq [t]
let (mk_sq_eq :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      let eq =
        FStarC_Reflection_V1_Builtins.pack_ln
          (FStarC_Reflection_V1_Data.Tv_FVar
             (FStarC_Reflection_V1_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) in
      mk_squash (FStar_Reflection_V1_Derived.mk_e_app eq [t1; t2])
let (grewrite :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = tcut (mk_sq_eq t1 t2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (641)) (Prims.of_int (12))
                 (Prims.of_int (641)) (Prims.of_int (33)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (641)) (Prims.of_int (36))
                 (Prims.of_int (655)) (Prims.of_int (44)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStarC_Reflection_V1_Builtins.pack_ln
                          (FStarC_Reflection_V1_Data.Tv_Var
                             (FStar_Reflection_V1_Derived.bv_of_binder e)))) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (642)) (Prims.of_int (12))
                            (Prims.of_int (642)) (Prims.of_int (45)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (643)) (Prims.of_int (4))
                            (Prims.of_int (655)) (Prims.of_int (44)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun e1 ->
                         Obj.magic
                           (pointwise
                              (fun uu___2 ->
                                 let uu___3 =
                                   let uu___4 =
                                     let uu___5 = cur_goal () in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V1.Derived.fst"
                                                (Prims.of_int (646))
                                                (Prims.of_int (30))
                                                (Prims.of_int (646))
                                                (Prims.of_int (42)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V1.Derived.fst"
                                                (Prims.of_int (646))
                                                (Prims.of_int (14))
                                                (Prims.of_int (646))
                                                (Prims.of_int (42)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             Obj.magic
                                               (FStar_Reflection_V1_Formula.term_as_formula
                                                  uu___6)) uu___6) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.V1.Derived.fst"
                                              (Prims.of_int (646))
                                              (Prims.of_int (14))
                                              (Prims.of_int (646))
                                              (Prims.of_int (42)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.V1.Derived.fst"
                                              (Prims.of_int (646))
                                              (Prims.of_int (8))
                                              (Prims.of_int (651))
                                              (Prims.of_int (20)))))
                                     (Obj.magic uu___4)
                                     (fun uu___5 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 ->
                                             match uu___5 with
                                             | FStar_Reflection_V1_Formula.Comp
                                                 (FStar_Reflection_V1_Formula.Eq
                                                  uu___7, lhs, rhs)
                                                 ->
                                                 (match FStarC_Reflection_V1_Builtins.inspect_ln
                                                          lhs
                                                  with
                                                  | FStarC_Reflection_V1_Data.Tv_Uvar
                                                      (uu___8, uu___9) ->
                                                      true
                                                  | uu___8 -> false)
                                             | uu___7 -> false)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (646))
                                            (Prims.of_int (8))
                                            (Prims.of_int (651))
                                            (Prims.of_int (20)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V1.Derived.fst"
                                            (Prims.of_int (653))
                                            (Prims.of_int (6))
                                            (Prims.of_int (655))
                                            (Prims.of_int (43)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun is_uvar ->
                                         if is_uvar
                                         then Obj.magic (trefl ())
                                         else
                                           Obj.magic
                                             (try_with
                                                (fun uu___5 ->
                                                   match () with
                                                   | () -> exact e1)
                                                (fun uu___5 -> trefl ())))
                                        uu___4)))) uu___2))) uu___1)
let (grewrite_eq :
  FStarC_Reflection_Types.binder ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      FStar_Reflection_V1_Formula.term_as_formula
        (FStar_Reflection_V1_Derived.type_of_binder b) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (662)) (Prims.of_int (8)) (Prims.of_int (662))
               (Prims.of_int (42)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (662)) (Prims.of_int (2)) (Prims.of_int (674))
               (Prims.of_int (7))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V1_Formula.Comp
                (FStar_Reflection_V1_Formula.Eq uu___2, l, r) ->
                let uu___3 = grewrite l r in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (664)) (Prims.of_int (4))
                              (Prims.of_int (664)) (Prims.of_int (16)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (665)) (Prims.of_int (4))
                              (Prims.of_int (665)) (Prims.of_int (54)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           Obj.magic
                             (iseq
                                [idtac;
                                (fun uu___5 ->
                                   let uu___6 = binder_to_term b in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.V1.Derived.fst"
                                              (Prims.of_int (665))
                                              (Prims.of_int (34))
                                              (Prims.of_int (665))
                                              (Prims.of_int (52)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.V1.Derived.fst"
                                              (Prims.of_int (665))
                                              (Prims.of_int (28))
                                              (Prims.of_int (665))
                                              (Prims.of_int (52)))))
                                     (Obj.magic uu___6)
                                     (fun uu___7 ->
                                        (fun uu___7 ->
                                           Obj.magic (exact uu___7)) uu___7))]))
                          uu___4))
            | uu___2 ->
                let uu___3 =
                  FStar_Reflection_V1_Formula.term_as_formula'
                    (FStar_Reflection_V1_Derived.type_of_binder b) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (667)) (Prims.of_int (16))
                              (Prims.of_int (667)) (Prims.of_int (51)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (667)) (Prims.of_int (10))
                              (Prims.of_int (673)) (Prims.of_int (56)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           match uu___4 with
                           | FStar_Reflection_V1_Formula.Comp
                               (FStar_Reflection_V1_Formula.Eq uu___5, l, r)
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___6 = grewrite l r in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V1.Derived.fst"
                                                (Prims.of_int (669))
                                                (Prims.of_int (6))
                                                (Prims.of_int (669))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V1.Derived.fst"
                                                (Prims.of_int (670))
                                                (Prims.of_int (6))
                                                (Prims.of_int (671))
                                                (Prims.of_int (56)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             Obj.magic
                                               (iseq
                                                  [idtac;
                                                  (fun uu___8 ->
                                                     let uu___9 =
                                                       apply_lemma
                                                         (FStarC_Reflection_V2_Builtins.pack_ln
                                                            (FStarC_Reflection_V2_Data.Tv_FVar
                                                               (FStarC_Reflection_V2_Builtins.pack_fv
                                                                  ["FStar";
                                                                  "Tactics";
                                                                  "V1";
                                                                  "Derived";
                                                                  "__un_sq_eq"]))) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V1.Derived.fst"
                                                                (Prims.of_int (670))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (670))
                                                                (Prims.of_int (55)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V1.Derived.fst"
                                                                (Prims.of_int (671))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (671))
                                                                (Prims.of_int (54)))))
                                                       (Obj.magic uu___9)
                                                       (fun uu___10 ->
                                                          (fun uu___10 ->
                                                             let uu___11 =
                                                               binder_to_term
                                                                 b in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (54)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (54)))))
                                                                  (Obj.magic
                                                                    uu___11)
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (exact
                                                                    uu___12))
                                                                    uu___12)))
                                                            uu___10))]))
                                            uu___7)))
                           | uu___5 ->
                               Obj.magic
                                 (Obj.repr
                                    (fail
                                       "grewrite_eq: binder type is not an equality")))
                          uu___4))) uu___1)
let rec (apply_squash_or_lem :
  Prims.nat ->
    FStarC_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun t ->
      try_with (fun uu___ -> match () with | () -> apply t)
        (fun uu___ ->
           try_with
             (fun uu___1 ->
                match () with
                | () ->
                    let uu___2 =
                      apply
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar"; "Squash"; "return_squash"]))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V1.Derived.fst"
                               (Prims.of_int (696)) (Prims.of_int (8))
                               (Prims.of_int (696)) (Prims.of_int (43)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V1.Derived.fst"
                               (Prims.of_int (696)) (Prims.of_int (45))
                               (Prims.of_int (696)) (Prims.of_int (52)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 -> Obj.magic (apply t)) uu___3))
             (fun uu___1 ->
                try_with (fun uu___2 -> match () with | () -> apply_lemma t)
                  (fun uu___2 ->
                     (fun uu___2 ->
                        if d <= Prims.int_zero
                        then
                          Obj.magic (Obj.repr (fail "mapply: out of fuel"))
                        else
                          Obj.magic
                            (Obj.repr
                               (let uu___4 =
                                  let uu___5 = cur_env () in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V1.Derived.fst"
                                             (Prims.of_int (702))
                                             (Prims.of_int (16))
                                             (Prims.of_int (702))
                                             (Prims.of_int (28)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V1.Derived.fst"
                                             (Prims.of_int (702))
                                             (Prims.of_int (13))
                                             (Prims.of_int (702))
                                             (Prims.of_int (30)))))
                                    (Obj.magic uu___5)
                                    (fun uu___6 ->
                                       (fun uu___6 ->
                                          Obj.magic
                                            (FStarC_Tactics_V1_Builtins.tc
                                               uu___6 t)) uu___6) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (702))
                                           (Prims.of_int (13))
                                           (Prims.of_int (702))
                                           (Prims.of_int (30)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (702))
                                           (Prims.of_int (33))
                                           (Prims.of_int (751))
                                           (Prims.of_int (41)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun ty ->
                                        let uu___5 =
                                          FStar_Tactics_V1_SyntaxHelpers.collect_arr
                                            ty in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V1.Derived.fst"
                                                      (Prims.of_int (703))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (703))
                                                      (Prims.of_int (31)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V1.Derived.fst"
                                                      (Prims.of_int (702))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (751))
                                                      (Prims.of_int (41)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   match uu___6 with
                                                   | (tys, c) ->
                                                       (match FStarC_Reflection_V1_Builtins.inspect_comp
                                                                c
                                                        with
                                                        | FStarC_Reflection_V1_Data.C_Lemma
                                                            (pre, post,
                                                             uu___7)
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    (post,
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (32)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    post1 ->
                                                                    let uu___9
                                                                    =
                                                                    norm_term
                                                                    [] post1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    post2 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Reflection_V1_Formula.term_as_formula'
                                                                    post2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V1_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___12
                                                                    =
                                                                    apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V1";
                                                                    "Derived";
                                                                    "push1"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___13)))
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (fail
                                                                    "mapply: can't apply (1)")))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                        | FStarC_Reflection_V1_Data.C_Total
                                                            rt ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (match 
                                                                    FStar_Reflection_V1_Derived.unsquash_term
                                                                    rt
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    rt1 ->
                                                                    let uu___7
                                                                    =
                                                                    norm_term
                                                                    [] rt1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun rt2
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Reflection_V1_Formula.term_as_formula'
                                                                    rt2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V1_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V1";
                                                                    "Derived";
                                                                    "push1"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___11)))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (fail
                                                                    "mapply: can't apply (1)")))
                                                                    uu___9)))
                                                                    uu___8)
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    norm_term
                                                                    [] rt in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (748))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun rt1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Reflection_V1_Formula.term_as_formula'
                                                                    rt1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (748))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V1_Formula.Implies
                                                                    (p, q) ->
                                                                    let uu___10
                                                                    =
                                                                    apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V1";
                                                                    "Derived";
                                                                    "push1"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___11))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Squash";
                                                                    "return_squash"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (748))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (748))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (apply t))
                                                                    uu___12)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                        | uu___7 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (fail
                                                                    "mapply: can't apply (2)"))))
                                                  uu___6))) uu___5)))) uu___2)))
let (mapply :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> apply_squash_or_lem (Prims.of_int (10)) t
let (admit_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V1_Builtins.dump "Admitting" in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (761)) (Prims.of_int (2)) (Prims.of_int (761))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (762)) (Prims.of_int (2)) (Prims.of_int (762))
               (Prims.of_int (16))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            Obj.magic
              (apply
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["Prims"; "admit"]))))) uu___2)
let admit_dump : 'a . (unit -> 'a) -> unit -> 'a = fun x -> fun uu___ -> x ()
let (magic_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V1_Builtins.dump "Admitting" in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (769)) (Prims.of_int (2)) (Prims.of_int (769))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (770)) (Prims.of_int (2)) (Prims.of_int (772))
               (Prims.of_int (4))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 =
              apply
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["Prims"; "magic"]))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (770)) (Prims.of_int (2))
                          (Prims.of_int (770)) (Prims.of_int (16)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (771)) (Prims.of_int (2))
                          (Prims.of_int (772)) (Prims.of_int (4)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       let uu___5 =
                         exact
                           (FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_Const
                                 FStarC_Reflection_V2_Data.C_Unit)) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (771)) (Prims.of_int (2))
                                     (Prims.of_int (771)) (Prims.of_int (13)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (772)) (Prims.of_int (2))
                                     (Prims.of_int (772)) (Prims.of_int (4)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___7 -> ())))) uu___4))) uu___2)
let magic_dump : 'a . 'a -> unit -> 'a = fun x -> fun uu___ -> x
let (change_with :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      focus
        (fun uu___ ->
           let uu___1 = grewrite t1 t2 in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                      (Prims.of_int (779)) (Prims.of_int (8))
                      (Prims.of_int (779)) (Prims.of_int (22)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                      (Prims.of_int (780)) (Prims.of_int (8))
                      (Prims.of_int (780)) (Prims.of_int (29)))))
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun uu___2 -> Obj.magic (iseq [idtac; trivial])) uu___2))
let (change_sq :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    FStarC_Tactics_V1_Builtins.change
      (FStar_Reflection_V1_Derived.mk_e_app
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "squash"])))
         [t1])
let finish_by :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    let uu___ = t () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (787)) (Prims.of_int (12)) (Prims.of_int (787))
               (Prims.of_int (16)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (788)) (Prims.of_int (4)) (Prims.of_int (789))
               (Prims.of_int (5))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun x ->
            let uu___1 =
              or_else qed
                (fun uu___2 ->
                   (fun uu___2 -> Obj.magic (fail "finish_by: not finished"))
                     uu___2) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (788)) (Prims.of_int (4))
                          (Prims.of_int (788)) (Prims.of_int (58)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (787)) (Prims.of_int (8))
                          (Prims.of_int (787)) (Prims.of_int (9)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> x))))
           uu___1)
let solve_then :
  'a 'b .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
        ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t1 ->
    fun t2 ->
      let uu___ = FStarC_Tactics_V1_Builtins.dup () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (792)) (Prims.of_int (4)) (Prims.of_int (792))
                 (Prims.of_int (10)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (792)) (Prims.of_int (11))
                 (Prims.of_int (796)) (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 = focus (fun uu___3 -> finish_by t1) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (793)) (Prims.of_int (12))
                            (Prims.of_int (793)) (Prims.of_int (42)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                            (Prims.of_int (793)) (Prims.of_int (45))
                            (Prims.of_int (796)) (Prims.of_int (5)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun x ->
                         let uu___3 = t2 x in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V1.Derived.fst"
                                       (Prims.of_int (794))
                                       (Prims.of_int (12))
                                       (Prims.of_int (794))
                                       (Prims.of_int (16)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V1.Derived.fst"
                                       (Prims.of_int (795))
                                       (Prims.of_int (4))
                                       (Prims.of_int (796))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun y ->
                                    let uu___4 = trefl () in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V1.Derived.fst"
                                                  (Prims.of_int (795))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (795))
                                                  (Prims.of_int (12)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V1.Derived.fst"
                                                  (Prims.of_int (794))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (794))
                                                  (Prims.of_int (9)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 -> y)))) uu___4)))
                        uu___3))) uu___1)
let add_elem :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    focus
      (fun uu___ ->
         let uu___1 =
           apply
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Cons"]))) in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                    (Prims.of_int (799)) (Prims.of_int (4))
                    (Prims.of_int (799)) (Prims.of_int (17)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                    (Prims.of_int (800)) (Prims.of_int (4))
                    (Prims.of_int (804)) (Prims.of_int (5)))))
           (Obj.magic uu___1)
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (focus
                      (fun uu___3 ->
                         let uu___4 = t () in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V1.Derived.fst"
                                    (Prims.of_int (801)) (Prims.of_int (14))
                                    (Prims.of_int (801)) (Prims.of_int (18)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V1.Derived.fst"
                                    (Prims.of_int (802)) (Prims.of_int (6))
                                    (Prims.of_int (803)) (Prims.of_int (7)))))
                           (Obj.magic uu___4)
                           (fun uu___5 ->
                              (fun x ->
                                 let uu___5 = qed () in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V1.Derived.fst"
                                               (Prims.of_int (802))
                                               (Prims.of_int (6))
                                               (Prims.of_int (802))
                                               (Prims.of_int (12)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V1.Derived.fst"
                                               (Prims.of_int (801))
                                               (Prims.of_int (10))
                                               (Prims.of_int (801))
                                               (Prims.of_int (11)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___7 -> x)))) uu___5))))
                uu___2))
let specialize :
  'a .
    'a ->
      Prims.string Prims.list ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun l ->
      fun uu___ ->
        solve_then
          (fun uu___1 ->
             let uu___2 =
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___3 ->
                       (fun uu___3 ->
                          Obj.magic
                            (failwith
                               "Cannot evaluate open quotation at runtime"))
                         uu___3)) in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                        (Prims.of_int (823)) (Prims.of_int (42))
                        (Prims.of_int (823)) (Prims.of_int (51)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                        (Prims.of_int (823)) (Prims.of_int (36))
                        (Prims.of_int (823)) (Prims.of_int (51)))))
               (Obj.magic uu___2)
               (fun uu___3 -> (fun uu___3 -> Obj.magic (exact uu___3)) uu___3))
          (fun uu___1 ->
             FStarC_Tactics_V1_Builtins.norm
               [FStar_Pervasives.delta_only l;
               FStar_Pervasives.iota;
               FStar_Pervasives.zeta])
let (tlabel : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (826)) (Prims.of_int (10)) (Prims.of_int (826))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (826)) (Prims.of_int (4)) (Prims.of_int (829))
               (Prims.of_int (38))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (Obj.repr (fail "tlabel: no goals"))
            | h::t ->
                Obj.magic
                  (Obj.repr
                     (FStarC_Tactics_V1_Builtins.set_goals
                        ((FStarC_Tactics_Types.set_label l h) :: t)))) uu___1)
let (tlabel' : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (832)) (Prims.of_int (10)) (Prims.of_int (832))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (832)) (Prims.of_int (4)) (Prims.of_int (836))
               (Prims.of_int (26))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (Obj.repr (fail "tlabel': no goals"))
            | h::t ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                FStarC_Tactics_Types.set_label
                                  (Prims.strcat l
                                     (FStarC_Tactics_Types.get_label h)) h)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (835)) (Prims.of_int (16))
                                 (Prims.of_int (835)) (Prims.of_int (45)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (836)) (Prims.of_int (8))
                                 (Prims.of_int (836)) (Prims.of_int (26)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun h1 ->
                              Obj.magic
                                (FStarC_Tactics_V1_Builtins.set_goals (h1 ::
                                   t))) uu___3)))) uu___1)
let (focus_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        let uu___3 = goals () in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                   (Prims.of_int (839)) (Prims.of_int (15))
                   (Prims.of_int (839)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                   (Prims.of_int (839)) (Prims.of_int (14))
                   (Prims.of_int (839)) (Prims.of_int (39)))))
          (Obj.magic uu___3)
          (fun uu___4 ->
             (fun uu___4 ->
                let uu___5 = smt_goals () in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (839)) (Prims.of_int (26))
                              (Prims.of_int (839)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (839)) (Prims.of_int (14))
                              (Prims.of_int (839)) (Prims.of_int (39)))))
                     (Obj.magic uu___5)
                     (fun uu___6 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___7 -> (op_At ()) uu___4 uu___6)))) uu___4) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (839)) (Prims.of_int (14))
                 (Prims.of_int (839)) (Prims.of_int (39)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (839)) (Prims.of_int (4)) (Prims.of_int (839))
                 (Prims.of_int (39))))) (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              Obj.magic (FStarC_Tactics_V1_Builtins.set_goals uu___3)) uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (839)) (Prims.of_int (4)) (Prims.of_int (839))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (840)) (Prims.of_int (4)) (Prims.of_int (840))
               (Prims.of_int (20))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            Obj.magic (FStarC_Tactics_V1_Builtins.set_smt_goals [])) uu___2)
let rec extract_nth :
  'a .
    Prims.nat ->
      'a Prims.list -> ('a * 'a Prims.list) FStar_Pervasives_Native.option
  =
  fun n ->
    fun l ->
      match (n, l) with
      | (uu___, []) -> FStar_Pervasives_Native.None
      | (uu___, hd::tl) when uu___ = Prims.int_zero ->
          FStar_Pervasives_Native.Some (hd, tl)
      | (uu___, hd::tl) ->
          (match extract_nth (n - Prims.int_one) tl with
           | FStar_Pervasives_Native.Some (hd', tl') ->
               FStar_Pervasives_Native.Some (hd', (hd :: tl'))
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (bump_nth : Prims.pos -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun n ->
    let uu___ =
      let uu___1 = goals () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (855)) (Prims.of_int (28))
                 (Prims.of_int (855)) (Prims.of_int (38)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (855)) (Prims.of_int (8)) (Prims.of_int (855))
                 (Prims.of_int (38))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> extract_nth (n - Prims.int_one) uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (855)) (Prims.of_int (8)) (Prims.of_int (855))
               (Prims.of_int (38)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (855)) (Prims.of_int (2)) (Prims.of_int (857))
               (Prims.of_int (37))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                Obj.magic (Obj.repr (fail "bump_nth: not that many goals"))
            | FStar_Pervasives_Native.Some (h, t) ->
                Obj.magic
                  (Obj.repr (FStarC_Tactics_V1_Builtins.set_goals (h :: t))))
           uu___1)
let rec (destruct_list :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_V1_SyntaxHelpers.collect_app t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (860)) (Prims.of_int (21)) (Prims.of_int (860))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (859)) (Prims.of_int (52)) (Prims.of_int (872))
               (Prims.of_int (27))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (head, args) ->
                (match ((FStarC_Reflection_V1_Builtins.inspect_ln head),
                         args)
                 with
                 | (FStarC_Reflection_V1_Data.Tv_FVar fv,
                    (a1, FStarC_Reflection_V1_Data.Q_Explicit)::(a2,
                                                                 FStarC_Reflection_V1_Data.Q_Explicit)::[])
                     ->
                     Obj.magic
                       (Obj.repr
                          (if
                             (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.cons_qn
                           then
                             Obj.repr
                               (let uu___2 = destruct_list a2 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (865))
                                           (Prims.of_int (17))
                                           (Prims.of_int (865))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (865))
                                           (Prims.of_int (11))
                                           (Prims.of_int (865))
                                           (Prims.of_int (33)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> a1 :: uu___3)))
                           else
                             Obj.repr
                               (FStar_Tactics_Effect.raise
                                  FStarC_Tactics_Common.NotAListLiteral)))
                 | (FStarC_Reflection_V1_Data.Tv_FVar fv,
                    (uu___2, FStarC_Reflection_V1_Data.Q_Implicit)::(a1,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)::
                    (a2, FStarC_Reflection_V1_Data.Q_Explicit)::[]) ->
                     Obj.magic
                       (Obj.repr
                          (if
                             (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.cons_qn
                           then
                             Obj.repr
                               (let uu___3 = destruct_list a2 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (865))
                                           (Prims.of_int (17))
                                           (Prims.of_int (865))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V1.Derived.fst"
                                           (Prims.of_int (865))
                                           (Prims.of_int (11))
                                           (Prims.of_int (865))
                                           (Prims.of_int (33)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___5 -> a1 :: uu___4)))
                           else
                             Obj.repr
                               (FStar_Tactics_Effect.raise
                                  FStarC_Tactics_Common.NotAListLiteral)))
                 | (FStarC_Reflection_V1_Data.Tv_FVar fv, uu___2) ->
                     Obj.magic
                       (Obj.repr
                          (if
                             (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.nil_qn
                           then
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> [])
                           else
                             FStar_Tactics_Effect.raise
                               FStarC_Tactics_Common.NotAListLiteral))
                 | uu___2 ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.raise
                             FStarC_Tactics_Common.NotAListLiteral)))) uu___1)
let (get_match_body :
  unit -> (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      let uu___2 = cur_goal () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (875)) (Prims.of_int (22))
                 (Prims.of_int (875)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                 (Prims.of_int (875)) (Prims.of_int (8)) (Prims.of_int (875))
                 (Prims.of_int (35))))) (Obj.magic uu___2)
        (fun uu___3 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___4 -> FStar_Reflection_V1_Derived.unsquash_term uu___3)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (875)) (Prims.of_int (8)) (Prims.of_int (875))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (875)) (Prims.of_int (2)) (Prims.of_int (879))
               (Prims.of_int (46))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | FStar_Pervasives_Native.None -> Obj.magic (Obj.repr (fail ""))
            | FStar_Pervasives_Native.Some t ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        FStar_Tactics_V1_SyntaxHelpers.inspect_unascribe t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (877)) (Prims.of_int (20))
                                 (Prims.of_int (877)) (Prims.of_int (39)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V1.Derived.fst"
                                 (Prims.of_int (877)) (Prims.of_int (14))
                                 (Prims.of_int (879)) (Prims.of_int (46)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           match uu___4 with
                           | FStarC_Reflection_V1_Data.Tv_Match
                               (sc, uu___5, uu___6) ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___7 -> sc)
                           | uu___5 -> fail "Goal is not a match")))) uu___2)
let rec last : 'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun x ->
       match x with
       | [] -> Obj.magic (Obj.repr (fail "last: empty list"))
       | x1::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x1)))
       | uu___::xs -> Obj.magic (Obj.repr (last xs))) uu___
let (branch_on_match : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    focus
      (fun uu___1 ->
         let uu___2 = get_match_body () in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                    (Prims.of_int (892)) (Prims.of_int (14))
                    (Prims.of_int (892)) (Prims.of_int (31)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                    (Prims.of_int (892)) (Prims.of_int (34))
                    (Prims.of_int (898)) (Prims.of_int (20)))))
           (Obj.magic uu___2)
           (fun uu___3 ->
              (fun x ->
                 let uu___3 = FStarC_Tactics_V1_Builtins.t_destruct x in
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V1.Derived.fst"
                               (Prims.of_int (893)) (Prims.of_int (14))
                               (Prims.of_int (893)) (Prims.of_int (26)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V1.Derived.fst"
                               (Prims.of_int (894)) (Prims.of_int (6))
                               (Prims.of_int (898)) (Prims.of_int (20)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            Obj.magic
                              (iterAll
                                 (fun uu___5 ->
                                    let uu___6 =
                                      repeat FStarC_Tactics_V1_Builtins.intro in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V1.Derived.fst"
                                               (Prims.of_int (895))
                                               (Prims.of_int (17))
                                               (Prims.of_int (895))
                                               (Prims.of_int (29)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V1.Derived.fst"
                                               (Prims.of_int (895))
                                               (Prims.of_int (32))
                                               (Prims.of_int (898))
                                               (Prims.of_int (19)))))
                                      (Obj.magic uu___6)
                                      (fun uu___7 ->
                                         (fun bs ->
                                            let uu___7 = last bs in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.V1.Derived.fst"
                                                          (Prims.of_int (896))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (896))
                                                          (Prims.of_int (23)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.V1.Derived.fst"
                                                          (Prims.of_int (897))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (898))
                                                          (Prims.of_int (19)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun b ->
                                                       let uu___8 =
                                                         grewrite_eq b in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (897))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (897))
                                                                    (Prims.of_int (21)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V1.Derived.fst"
                                                                    (Prims.of_int (898))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (898))
                                                                    (Prims.of_int (19)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               (fun uu___9 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Tactics_V1_Builtins.norm
                                                                    [FStar_Pervasives.iota]))
                                                                 uu___9)))
                                                      uu___8))) uu___7))))
                           uu___4))) uu___3))
let (nth_binder :
  Prims.int ->
    (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun i ->
    let uu___ = cur_binders () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (907)) (Prims.of_int (11)) (Prims.of_int (907))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
               (Prims.of_int (907)) (Prims.of_int (28)) (Prims.of_int (912))
               (Prims.of_int (15))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun bs ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      if i >= Prims.int_zero
                      then i
                      else (FStar_List_Tot_Base.length bs) + i)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (908)) (Prims.of_int (16))
                          (Prims.of_int (908)) (Prims.of_int (65)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                          (Prims.of_int (908)) (Prims.of_int (68))
                          (Prims.of_int (912)) (Prims.of_int (15)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun k ->
                       let uu___2 =
                         if k < Prims.int_zero
                         then Obj.magic (fail "not enough binders")
                         else
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 -> k)) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (909)) (Prims.of_int (16))
                                     (Prims.of_int (909)) (Prims.of_int (62)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V1.Derived.fst"
                                     (Prims.of_int (910)) (Prims.of_int (2))
                                     (Prims.of_int (912)) (Prims.of_int (15)))))
                            (Obj.magic uu___2)
                            (fun k1 ->
                               match FStar_List_Tot_Base.nth bs k1 with
                               | FStar_Pervasives_Native.None ->
                                   fail "not enough binders"
                               | FStar_Pervasives_Native.Some b ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> b)))) uu___2))) uu___1)
let rec (mk_abs :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun args ->
         fun t ->
           match args with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | a::args' ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = mk_abs args' t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.Derived.fst"
                                (Prims.of_int (919)) (Prims.of_int (13))
                                (Prims.of_int (919)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.Derived.fst"
                                (Prims.of_int (920)) (Prims.of_int (4))
                                (Prims.of_int (920)) (Prims.of_int (22)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun t' ->
                             Obj.magic
                               (FStarC_Tactics_V1_Builtins.pack
                                  (FStarC_Reflection_V1_Data.Tv_Abs (a, t'))))
                            uu___1)))) uu___1 uu___
let (string_to_term_with_lb :
  (Prims.string * FStarC_Reflection_Types.term) Prims.list ->
    FStarC_Reflection_Types.env ->
      Prims.string ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun letbindings ->
    fun e ->
      fun t ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStarC_Reflection_V2_Builtins.pack_ln
                    FStarC_Reflection_V2_Data.Tv_Unknown)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                   (Prims.of_int (928)) (Prims.of_int (14))
                   (Prims.of_int (928)) (Prims.of_int (32)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V1.Derived.fst"
                   (Prims.of_int (928)) (Prims.of_int (35))
                   (Prims.of_int (934)) (Prims.of_int (75)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun unk ->
                let uu___1 =
                  FStar_Tactics_Util.fold_left
                    (fun uu___2 ->
                       fun uu___3 ->
                         match (uu___2, uu___3) with
                         | ((e1, lb_bvs), (i, v)) ->
                             let uu___4 =
                               FStarC_Tactics_V1_Builtins.push_bv_dsenv e1 i in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.V1.Derived.fst"
                                        (Prims.of_int (930))
                                        (Prims.of_int (20))
                                        (Prims.of_int (930))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.V1.Derived.fst"
                                        (Prims.of_int (929))
                                        (Prims.of_int (56))
                                        (Prims.of_int (931))
                                        (Prims.of_int (25)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 ->
                                       match uu___5 with
                                       | (e2, bv) ->
                                           (e2, ((v, bv) :: lb_bvs)))))
                    (e, []) letbindings in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (929)) (Prims.of_int (20))
                              (Prims.of_int (932)) (Prims.of_int (27)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V1.Derived.fst"
                              (Prims.of_int (928)) (Prims.of_int (35))
                              (Prims.of_int (934)) (Prims.of_int (75)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           match uu___2 with
                           | (e1, lb_bvs) ->
                               let uu___3 =
                                 FStarC_Tactics_V1_Builtins.string_to_term e1
                                   t in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V1.Derived.fst"
                                             (Prims.of_int (933))
                                             (Prims.of_int (12))
                                             (Prims.of_int (933))
                                             (Prims.of_int (30)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V1.Derived.fst"
                                             (Prims.of_int (934))
                                             (Prims.of_int (4))
                                             (Prims.of_int (934))
                                             (Prims.of_int (75)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun t1 ->
                                          Obj.magic
                                            (FStar_Tactics_Util.fold_left
                                               (fun t2 ->
                                                  fun uu___4 ->
                                                    match uu___4 with
                                                    | (i, bv) ->
                                                        FStarC_Tactics_V1_Builtins.pack
                                                          (FStarC_Reflection_V1_Data.Tv_Let
                                                             (false, [], bv,
                                                               unk, i, t2)))
                                               t1 lb_bvs)) uu___4))) uu___2)))
               uu___1)
let (trans : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V1"; "Derived"; "lem_trans"])))