open Prims
exception Goal_not_trivial 
let (uu___is_Goal_not_trivial : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Goal_not_trivial -> true | uu___ -> false
let rec (inspect_unascribe :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Data.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (34))
         (Prims.of_int (8)) (Prims.of_int (34)) (Prims.of_int (17)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (34))
         (Prims.of_int (2)) (Prims.of_int (38)) (Prims.of_int (12)))
      (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_AscribedT (t1, uu___1, uu___2, uu___3)
                -> Obj.magic (Obj.repr (inspect_unascribe t1))
            | FStar_Reflection_Data.Tv_AscribedC (t1, uu___1, uu___2, uu___3)
                -> Obj.magic (Obj.repr (inspect_unascribe t1))
            | tv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> tv))))
           uu___)
let (goals :
  unit ->
    (FStar_Tactics_Types.goal Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (40))
         (Prims.of_int (42)) (Prims.of_int (40)) (Prims.of_int (50)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (40))
         (Prims.of_int (33)) (Prims.of_int (40)) (Prims.of_int (50)))
      (Obj.magic (FStar_Tactics_Effect.get ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goals_of uu___1))
let (smt_goals :
  unit ->
    (FStar_Tactics_Types.goal Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (41))
         (Prims.of_int (50)) (Prims.of_int (41)) (Prims.of_int (58)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (41))
         (Prims.of_int (37)) (Prims.of_int (41)) (Prims.of_int (58)))
      (Obj.magic (FStar_Tactics_Effect.get ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.smt_goals_of uu___1))
let fail : 'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun m -> FStar_Tactics_Effect.raise (FStar_Tactics_Common.TacticFailure m)
let fail_silently :
  'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (49))
         (Prims.of_int (4)) (Prims.of_int (49)) (Prims.of_int (17)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (50))
         (Prims.of_int (4)) (Prims.of_int (50)) (Prims.of_int (30)))
      (Obj.magic (FStar_Tactics_Builtins.set_urgency Prims.int_zero))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.raise
                 (FStar_Tactics_Common.TacticFailure m))) uu___)
let (_cur_goal :
  unit -> (FStar_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (54))
         (Prims.of_int (10)) (Prims.of_int (54)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (54))
         (Prims.of_int (4)) (Prims.of_int (56)) (Prims.of_int (15)))
      (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (Obj.repr (fail "no more goals"))
            | g::uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> g))))
           uu___1)
let (cur_env :
  unit -> (FStar_Reflection_Types.env, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (59))
         (Prims.of_int (36)) (Prims.of_int (59)) (Prims.of_int (50)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (59))
         (Prims.of_int (27)) (Prims.of_int (59)) (Prims.of_int (50)))
      (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goal_env uu___1))
let (cur_goal :
  unit -> (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (62))
         (Prims.of_int (38)) (Prims.of_int (62)) (Prims.of_int (52)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (62))
         (Prims.of_int (28)) (Prims.of_int (62)) (Prims.of_int (52)))
      (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goal_type uu___1))
let (cur_witness :
  unit -> (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (65))
         (Prims.of_int (45)) (Prims.of_int (65)) (Prims.of_int (59)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (65))
         (Prims.of_int (32)) (Prims.of_int (65)) (Prims.of_int (59)))
      (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goal_witness uu___1))
let (cur_goal_safe :
  unit -> (FStar_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (72))
         (Prims.of_int (9)) (Prims.of_int (72)) (Prims.of_int (26)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (72))
         (Prims.of_int (3)) (Prims.of_int (73)) (Prims.of_int (16)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (72))
               (Prims.of_int (18)) (Prims.of_int (72)) (Prims.of_int (26)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (72))
               (Prims.of_int (9)) (Prims.of_int (72)) (Prims.of_int (26)))
            (Obj.magic (FStar_Tactics_Effect.get ()))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 -> FStar_Tactics_Types.goals_of uu___1))))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> match uu___1 with | g::uu___3 -> g))
let (cur_binders :
  unit ->
    (FStar_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (77))
         (Prims.of_int (19)) (Prims.of_int (77)) (Prims.of_int (31)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (77))
         (Prims.of_int (4)) (Prims.of_int (77)) (Prims.of_int (31)))
      (Obj.magic (cur_env ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Reflection_Builtins.binders_of_env uu___1))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun pol ->
    fun f ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (81))
           (Prims.of_int (18)) (Prims.of_int (81)) (Prims.of_int (37)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (82))
           (Prims.of_int (4)) (Prims.of_int (85)) (Prims.of_int (5)))
        (Obj.magic (FStar_Tactics_Builtins.get_guard_policy ()))
        (fun uu___ ->
           (fun old_pol ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (82)) (Prims.of_int (4))
                      (Prims.of_int (82)) (Prims.of_int (24)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (83)) (Prims.of_int (4))
                      (Prims.of_int (85)) (Prims.of_int (5)))
                   (Obj.magic (FStar_Tactics_Builtins.set_guard_policy pol))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (83)) (Prims.of_int (12))
                                 (Prims.of_int (83)) (Prims.of_int (16)))
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (84)) (Prims.of_int (4))
                                 (Prims.of_int (85)) (Prims.of_int (5)))
                              (Obj.magic (f ()))
                              (fun uu___1 ->
                                 (fun r ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (84))
                                            (Prims.of_int (4))
                                            (Prims.of_int (84))
                                            (Prims.of_int (28)))
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (83))
                                            (Prims.of_int (8))
                                            (Prims.of_int (83))
                                            (Prims.of_int (9)))
                                         (Obj.magic
                                            (FStar_Tactics_Builtins.set_guard_policy
                                               old_pol))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 -> r)))) uu___1)))
                        uu___))) uu___)
let (exact :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu___ -> FStar_Tactics_Builtins.t_exact true false t)
let (exact_with_ref :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu___ -> FStar_Tactics_Builtins.t_exact true true t)
let (trivial : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (99))
         (Prims.of_int (2)) (Prims.of_int (99)) (Prims.of_int (61)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (100))
         (Prims.of_int (2)) (Prims.of_int (103)) (Prims.of_int (31)))
      (Obj.magic
         (FStar_Tactics_Builtins.norm
            [FStar_Pervasives.iota;
            FStar_Pervasives.zeta;
            FStar_Pervasives.reify_;
            FStar_Pervasives.delta;
            FStar_Pervasives.primops;
            FStar_Pervasives.simplify;
            FStar_Pervasives.unmeta]))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (100)) (Prims.of_int (10))
                    (Prims.of_int (100)) (Prims.of_int (21)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (101)) (Prims.of_int (2))
                    (Prims.of_int (103)) (Prims.of_int (31)))
                 (Obj.magic (cur_goal ()))
                 (fun uu___2 ->
                    (fun g ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (101)) (Prims.of_int (8))
                               (Prims.of_int (101)) (Prims.of_int (25)))
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (101)) (Prims.of_int (2))
                               (Prims.of_int (103)) (Prims.of_int (31)))
                            (Obj.magic
                               (FStar_Reflection_Formula.term_as_formula g))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | FStar_Reflection_Formula.True_ ->
                                      Obj.magic
                                        (exact
                                           (FStar_Reflection_Builtins.pack_ln
                                              (FStar_Reflection_Data.Tv_Const
                                                 FStar_Reflection_Data.C_Unit)))
                                  | uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.raise
                                           Goal_not_trivial)) uu___2)))
                      uu___2))) uu___1)
let (dismiss : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (115))
         (Prims.of_int (10)) (Prims.of_int (115)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (115))
         (Prims.of_int (4)) (Prims.of_int (117)) (Prims.of_int (27)))
      (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (fail "dismiss: no more goals")
            | uu___2::gs -> Obj.magic (FStar_Tactics_Builtins.set_goals gs))
           uu___1)
let (flip : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (121))
         (Prims.of_int (13)) (Prims.of_int (121)) (Prims.of_int (21)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (122))
         (Prims.of_int (4)) (Prims.of_int (124)) (Prims.of_int (42)))
      (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun gs ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (122)) (Prims.of_int (10))
                    (Prims.of_int (122)) (Prims.of_int (18)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (122)) (Prims.of_int (4))
                    (Prims.of_int (124)) (Prims.of_int (42)))
                 (Obj.magic (goals ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | [] -> Obj.magic (fail "flip: less than two goals")
                       | uu___2::[] ->
                           Obj.magic (fail "flip: less than two goals")
                       | g1::g2::gs1 ->
                           Obj.magic
                             (FStar_Tactics_Builtins.set_goals (g2 :: g1 ::
                                gs1))) uu___1))) uu___1)
let (qed : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (128))
         (Prims.of_int (10)) (Prims.of_int (128)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (128))
         (Prims.of_int (4)) (Prims.of_int (130)) (Prims.of_int (32)))
      (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())))
            | uu___2 -> Obj.magic (Obj.repr (fail "qed: not done!"))) uu___1)
let (debug : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (136))
         (Prims.of_int (7)) (Prims.of_int (136)) (Prims.of_int (19)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (136))
         (Prims.of_int (4)) (Prims.of_int (136)) (Prims.of_int (32)))
      (Obj.magic (FStar_Tactics_Builtins.debugging ()))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then Obj.magic (Obj.repr (FStar_Tactics_Builtins.print m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let (smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (143))
         (Prims.of_int (10)) (Prims.of_int (143)) (Prims.of_int (32)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (143))
         (Prims.of_int (4)) (Prims.of_int (149)) (Prims.of_int (11)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (143))
               (Prims.of_int (10)) (Prims.of_int (143)) (Prims.of_int (18)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (143))
               (Prims.of_int (10)) (Prims.of_int (143)) (Prims.of_int (32)))
            (Obj.magic (goals ()))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (143)) (Prims.of_int (20))
                          (Prims.of_int (143)) (Prims.of_int (32)))
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (143)) (Prims.of_int (10))
                          (Prims.of_int (143)) (Prims.of_int (32)))
                       (Obj.magic (smt_goals ()))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> (uu___1, uu___2))))) uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | ([], uu___2) -> Obj.magic (fail "smt: no active goals")
            | (g::gs, gs') ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (147)) (Prims.of_int (8))
                        (Prims.of_int (147)) (Prims.of_int (20)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (148)) (Prims.of_int (8))
                        (Prims.of_int (148)) (Prims.of_int (32)))
                     (Obj.magic (FStar_Tactics_Builtins.set_goals gs))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (FStar_Tactics_Builtins.set_smt_goals (g :: gs')))
                          uu___2))) uu___1)
let (idtac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
      uu___
let (later : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (155))
         (Prims.of_int (10)) (Prims.of_int (155)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (155))
         (Prims.of_int (4)) (Prims.of_int (157)) (Prims.of_int (33)))
      (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | g::gs ->
                Obj.magic
                  (FStar_Tactics_Builtins.set_goals
                     (FStar_List_Tot_Base.op_At gs [g]))
            | uu___2 -> Obj.magic (fail "later: no goals")) uu___1)
let (apply :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Builtins.t_apply true false false t
let (apply_noinst :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Builtins.t_apply true true false t
let (apply_lemma :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Builtins.t_apply_lemma false false t
let (trefl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_Builtins.t_trefl false
let (trefl_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_Builtins.t_trefl true
let (commute_applied_match :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_Builtins.t_commute_applied_match ()
let (apply_lemma_noinst :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Builtins.t_apply_lemma true false t
let (apply_lemma_rw :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Builtins.t_apply_lemma false true t
let (apply_raw :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Builtins.t_apply false false false t
let (exact_guard :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStar_Tactics_Types.Goal
      (fun uu___ -> FStar_Tactics_Builtins.t_exact true false t)
let (t_pointwise :
  FStar_Tactics_Types.direction ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun tau ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (216))
           (Prims.of_int (4)) (Prims.of_int (216)) (Prims.of_int (18)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (218))
           (Prims.of_int (2)) (Prims.of_int (221)) (Prims.of_int (24)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun uu___ ->
                (fun uu___ ->
                   fun t ->
                     Obj.magic
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> (true, FStar_Tactics_Types.Continue))))
                  uu___1 uu___))
        (fun uu___ ->
           (fun ctrl ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (219)) (Prims.of_int (4))
                      (Prims.of_int (219)) (Prims.of_int (10)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (221)) (Prims.of_int (2))
                      (Prims.of_int (221)) (Prims.of_int (24)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> fun uu___1 -> tau ()))
                   (fun uu___ ->
                      (fun rw ->
                         Obj.magic
                           (FStar_Tactics_Builtins.ctrl_rewrite d ctrl rw))
                        uu___))) uu___)
let (topdown_rewrite :
  (FStar_Reflection_Types.term ->
     ((Prims.bool * Prims.int), unit) FStar_Tactics_Effect.tac_repr)
    ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ctrl ->
    fun rw ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (246))
           (Prims.of_int (6)) (Prims.of_int (254)) (Prims.of_int (10)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (256))
           (Prims.of_int (4)) (Prims.of_int (256)) (Prims.of_int (33)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t ->
                FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                     (Prims.of_int (246)) (Prims.of_int (17))
                     (Prims.of_int (246)) (Prims.of_int (23)))
                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                     (Prims.of_int (246)) (Prims.of_int (6))
                     (Prims.of_int (254)) (Prims.of_int (10)))
                  (Obj.magic (ctrl t))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | (b, i) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (248)) (Prims.of_int (8))
                                    (Prims.of_int (252)) (Prims.of_int (58)))
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (254)) (Prims.of_int (6))
                                    (Prims.of_int (254)) (Prims.of_int (10)))
                                 (match i with
                                  | uu___2 when uu___2 = Prims.int_zero ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 FStar_Tactics_Types.Continue)))
                                  | uu___2 when uu___2 = Prims.int_one ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 FStar_Tactics_Types.Skip)))
                                  | uu___2 when uu___2 = (Prims.of_int (2))
                                      ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 FStar_Tactics_Types.Abort)))
                                  | uu___2 ->
                                      Obj.magic
                                        (Obj.repr
                                           (fail
                                              "topdown_rewrite: bad value from ctrl")))
                                 (fun f ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> (b, f))))) uu___1)))
        (fun uu___ ->
           (fun ctrl' ->
              Obj.magic
                (FStar_Tactics_Builtins.ctrl_rewrite
                   FStar_Tactics_Types.TopDown ctrl' rw)) uu___)
let (pointwise :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun tau -> t_pointwise FStar_Tactics_Types.BottomUp tau
let (pointwise' :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun tau -> t_pointwise FStar_Tactics_Types.TopDown tau
let (cur_module :
  unit -> (FStar_Reflection_Types.name, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (262))
         (Prims.of_int (13)) (Prims.of_int (262)) (Prims.of_int (25)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (262))
         (Prims.of_int (4)) (Prims.of_int (262)) (Prims.of_int (25)))
      (Obj.magic (FStar_Tactics_Builtins.top_env ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Reflection_Builtins.moduleof uu___1))
let (open_modules :
  unit ->
    (FStar_Reflection_Types.name Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (265))
         (Prims.of_int (21)) (Prims.of_int (265)) (Prims.of_int (33)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (265))
         (Prims.of_int (4)) (Prims.of_int (265)) (Prims.of_int (33)))
      (Obj.magic (FStar_Tactics_Builtins.top_env ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Reflection_Builtins.env_open_modules uu___1))
let (fresh_uvar :
  FStar_Reflection_Types.typ FStar_Pervasives_Native.option ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (268))
         (Prims.of_int (12)) (Prims.of_int (268)) (Prims.of_int (22)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (269))
         (Prims.of_int (4)) (Prims.of_int (269)) (Prims.of_int (16)))
      (Obj.magic (cur_env ()))
      (fun uu___ ->
         (fun e -> Obj.magic (FStar_Tactics_Builtins.uvar_env e o)) uu___)
let (unify :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (272))
           (Prims.of_int (12)) (Prims.of_int (272)) (Prims.of_int (22)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (273))
           (Prims.of_int (4)) (Prims.of_int (273)) (Prims.of_int (21)))
        (Obj.magic (cur_env ()))
        (fun uu___ ->
           (fun e -> Obj.magic (FStar_Tactics_Builtins.unify_env e t1 t2))
             uu___)
let (unify_guard :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (276))
           (Prims.of_int (12)) (Prims.of_int (276)) (Prims.of_int (22)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (277))
           (Prims.of_int (4)) (Prims.of_int (277)) (Prims.of_int (27)))
        (Obj.magic (cur_env ()))
        (fun uu___ ->
           (fun e ->
              Obj.magic (FStar_Tactics_Builtins.unify_guard_env e t1 t2))
             uu___)
let (tmatch :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (280))
           (Prims.of_int (12)) (Prims.of_int (280)) (Prims.of_int (22)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (281))
           (Prims.of_int (4)) (Prims.of_int (281)) (Prims.of_int (21)))
        (Obj.magic (cur_env ()))
        (fun uu___ ->
           (fun e -> Obj.magic (FStar_Tactics_Builtins.match_env e t1 t2))
             uu___)
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
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (287))
             (Prims.of_int (4)) (Prims.of_int (288)) (Prims.of_int (31)))
          (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (289))
             (Prims.of_int (4)) (Prims.of_int (301)) (Prims.of_int (10)))
          (if n < Prims.int_zero
           then Obj.magic (Obj.repr (fail "divide: negative n"))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (289)) (Prims.of_int (18))
                        (Prims.of_int (289)) (Prims.of_int (40)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (289)) (Prims.of_int (4))
                        (Prims.of_int (301)) (Prims.of_int (10)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (289)) (Prims.of_int (18))
                              (Prims.of_int (289)) (Prims.of_int (26)))
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (289)) (Prims.of_int (18))
                              (Prims.of_int (289)) (Prims.of_int (40)))
                           (Obj.magic (goals ()))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (289))
                                         (Prims.of_int (28))
                                         (Prims.of_int (289))
                                         (Prims.of_int (40)))
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (289))
                                         (Prims.of_int (18))
                                         (Prims.of_int (289))
                                         (Prims.of_int (40)))
                                      (Obj.magic (smt_goals ()))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> (uu___1, uu___2)))))
                                uu___1)))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | (gs, sgs) ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (290))
                                       (Prims.of_int (19))
                                       (Prims.of_int (290))
                                       (Prims.of_int (45)))
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (290))
                                       (Prims.of_int (4))
                                       (Prims.of_int (301))
                                       (Prims.of_int (10)))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          FStar_List_Tot_Base.splitAt n gs))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match uu___2 with
                                          | (gs1, gs2) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (292))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (292))
                                                      (Prims.of_int (17)))
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (292))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (301))
                                                      (Prims.of_int (10)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Builtins.set_goals
                                                         gs1))
                                                   (fun uu___3 ->
                                                      (fun uu___3 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Derived.fst"
                                                                 (Prims.of_int (292))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (292))
                                                                 (Prims.of_int (35)))
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Derived.fst"
                                                                 (Prims.of_int (293))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (301))
                                                                 (Prims.of_int (10)))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Builtins.set_smt_goals
                                                                    []))
                                                              (fun uu___4 ->
                                                                 (fun uu___4
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (16)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (l ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (28)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (goals ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (smt_goals
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (uu___5,
                                                                    uu___6)))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (gsl,
                                                                    sgsl) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (17)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    gs2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    []))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (16)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (r ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun y ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (28)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (goals ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (smt_goals
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (uu___8,
                                                                    uu___9)))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (gsr,
                                                                    sgsr) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (25)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    gsl gsr)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    sgs
                                                                    (FStar_List_Tot_Base.op_At
                                                                    sgsl sgsr))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> (x, y)))))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                   uu___4)))
                                                        uu___3))) uu___2)))
                          uu___1))) uu___)
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
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (305)) (Prims.of_int (23))
                      (Prims.of_int (305)) (Prims.of_int (53)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (305)) (Prims.of_int (57))
                      (Prims.of_int (305)) (Prims.of_int (59)))
                   (Obj.magic
                      (divide Prims.int_one t (fun uu___ -> iseq ts1)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
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
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (311))
         (Prims.of_int (10)) (Prims.of_int (311)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (311))
         (Prims.of_int (4)) (Prims.of_int (318)) (Prims.of_int (9)))
      (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] -> Obj.magic (fail "focus: no goals")
            | g::gs ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (314)) (Prims.of_int (18))
                        (Prims.of_int (314)) (Prims.of_int (30)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (315)) (Prims.of_int (8))
                        (Prims.of_int (318)) (Prims.of_int (9)))
                     (Obj.magic (smt_goals ()))
                     (fun uu___1 ->
                        (fun sgs ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (315)) (Prims.of_int (8))
                                   (Prims.of_int (315)) (Prims.of_int (21)))
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (315)) (Prims.of_int (23))
                                   (Prims.of_int (318)) (Prims.of_int (9)))
                                (Obj.magic
                                   (FStar_Tactics_Builtins.set_goals [g]))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (315))
                                              (Prims.of_int (23))
                                              (Prims.of_int (315))
                                              (Prims.of_int (39)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (316))
                                              (Prims.of_int (8))
                                              (Prims.of_int (318))
                                              (Prims.of_int (9)))
                                           (Obj.magic
                                              (FStar_Tactics_Builtins.set_smt_goals
                                                 []))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (316))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (316))
                                                         (Prims.of_int (20)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (317))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (318))
                                                         (Prims.of_int (9)))
                                                      (Obj.magic (t ()))
                                                      (fun uu___3 ->
                                                         (fun x ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33)))
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (9)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (27)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (goals ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___3 gs))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    uu___3))
                                                                    uu___3)))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (13)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (62)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (smt_goals
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___4
                                                                    sgs))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    x))))
                                                                    uu___3)))
                                                           uu___3))) uu___2)))
                                     uu___1))) uu___1))) uu___)
let (dump1 : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m -> focus (fun uu___ -> FStar_Tactics_Builtins.dump m)
let rec mapAll :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (324))
         (Prims.of_int (10)) (Prims.of_int (324)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (324))
         (Prims.of_int (4)) (Prims.of_int (326)) (Prims.of_int (66)))
      (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> [])))
            | uu___1::uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (326)) (Prims.of_int (27))
                           (Prims.of_int (326)) (Prims.of_int (58)))
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (326)) (Prims.of_int (14))
                           (Prims.of_int (326)) (Prims.of_int (66)))
                        (Obj.magic
                           (divide Prims.int_one t (fun uu___3 -> mapAll t)))
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 ->
                                match uu___3 with | (h, t1) -> h :: t1)))))
           uu___)
let rec (iterAll :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (330))
         (Prims.of_int (10)) (Prims.of_int (330)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (330))
         (Prims.of_int (4)) (Prims.of_int (332)) (Prims.of_int (60)))
      (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
            | uu___1::uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (332)) (Prims.of_int (22))
                           (Prims.of_int (332)) (Prims.of_int (54)))
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (332)) (Prims.of_int (58))
                           (Prims.of_int (332)) (Prims.of_int (60)))
                        (Obj.magic
                           (divide Prims.int_one t (fun uu___3 -> iterAll t)))
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> ()))))) uu___)
let (iterAllSMT :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (335))
         (Prims.of_int (18)) (Prims.of_int (335)) (Prims.of_int (40)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (335))
         (Prims.of_int (4)) (Prims.of_int (341)) (Prims.of_int (28)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (335))
               (Prims.of_int (18)) (Prims.of_int (335)) (Prims.of_int (26)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (335))
               (Prims.of_int (18)) (Prims.of_int (335)) (Prims.of_int (40)))
            (Obj.magic (goals ()))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (335)) (Prims.of_int (28))
                          (Prims.of_int (335)) (Prims.of_int (40)))
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (335)) (Prims.of_int (18))
                          (Prims.of_int (335)) (Prims.of_int (40)))
                       (Obj.magic (smt_goals ()))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> (uu___, uu___1))))) uu___)))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (gs, sgs) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (336)) (Prims.of_int (4))
                        (Prims.of_int (336)) (Prims.of_int (17)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (337)) (Prims.of_int (4))
                        (Prims.of_int (341)) (Prims.of_int (28)))
                     (Obj.magic (FStar_Tactics_Builtins.set_goals sgs))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (337)) (Prims.of_int (4))
                                   (Prims.of_int (337)) (Prims.of_int (20)))
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (338)) (Prims.of_int (4))
                                   (Prims.of_int (341)) (Prims.of_int (28)))
                                (Obj.magic
                                   (FStar_Tactics_Builtins.set_smt_goals []))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (338))
                                              (Prims.of_int (4))
                                              (Prims.of_int (338))
                                              (Prims.of_int (13)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (339))
                                              (Prims.of_int (4))
                                              (Prims.of_int (341))
                                              (Prims.of_int (28)))
                                           (Obj.magic (iterAll t))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (339))
                                                         (Prims.of_int (20))
                                                         (Prims.of_int (339))
                                                         (Prims.of_int (42)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (339))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (341))
                                                         (Prims.of_int (28)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (339))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (339))
                                                               (Prims.of_int (28)))
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (339))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (339))
                                                               (Prims.of_int (42)))
                                                            (Obj.magic
                                                               (goals ()))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (smt_goals
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (uu___4,
                                                                    uu___5)))))
                                                                 uu___4)))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match uu___4 with
                                                            | (gs', sgs') ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (16)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    gs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    gs' sgs')))
                                                                    uu___5)))
                                                           uu___4))) uu___3)))
                                     uu___2))) uu___1))) uu___)
let (seq :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      focus
        (fun uu___ ->
           FStar_Tactics_Effect.tac_bind
             (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (347))
                (Prims.of_int (21)) (Prims.of_int (347)) (Prims.of_int (25)))
             (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (347))
                (Prims.of_int (27)) (Prims.of_int (347)) (Prims.of_int (36)))
             (Obj.magic (f ()))
             (fun uu___1 -> (fun uu___1 -> Obj.magic (iterAll g)) uu___1))
let (exact_args :
  FStar_Reflection_Data.aqualv Prims.list ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun qs ->
    fun t ->
      focus
        (fun uu___ ->
           FStar_Tactics_Effect.tac_bind
             (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (351))
                (Prims.of_int (16)) (Prims.of_int (351)) (Prims.of_int (39)))
             (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (352))
                (Prims.of_int (8)) (Prims.of_int (357)) (Prims.of_int (44)))
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___1 -> FStar_List_Tot_Base.length qs))
             (fun uu___1 ->
                (fun n ->
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (352)) (Prims.of_int (18))
                           (Prims.of_int (352)) (Prims.of_int (55)))
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (353)) (Prims.of_int (8))
                           (Prims.of_int (357)) (Prims.of_int (44)))
                        (Obj.magic
                           (FStar_Tactics_Util.repeatn n
                              (fun uu___1 ->
                                 fresh_uvar FStar_Pervasives_Native.None)))
                        (fun uu___1 ->
                           (fun uvs ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (353))
                                      (Prims.of_int (17))
                                      (Prims.of_int (353))
                                      (Prims.of_int (38)))
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (354)) (Prims.of_int (8))
                                      (Prims.of_int (357))
                                      (Prims.of_int (44)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (353))
                                            (Prims.of_int (26))
                                            (Prims.of_int (353))
                                            (Prims.of_int (38)))
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (353))
                                            (Prims.of_int (17))
                                            (Prims.of_int (353))
                                            (Prims.of_int (38)))
                                         (Obj.magic
                                            (FStar_Tactics_Util.zip uvs qs))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 FStar_Reflection_Derived.mk_app
                                                   t uu___1))))
                                   (fun uu___1 ->
                                      (fun t' ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (354))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (354))
                                                 (Prims.of_int (16)))
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (355))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (357))
                                                 (Prims.of_int (44)))
                                              (Obj.magic (exact t'))
                                              (fun uu___1 ->
                                                 (fun uu___1 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Util.iter
                                                         (fun uu___2 ->
                                                            (fun uv ->
                                                               if
                                                                 FStar_Reflection_Derived.is_uvar
                                                                   uv
                                                               then
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Builtins.unshelve
                                                                    uv))
                                                               else
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                              uu___2)
                                                         (FStar_List_Tot_Base.rev
                                                            uvs))) uu___1)))
                                        uu___1))) uu___1))) uu___1))
let (exact_n :
  Prims.int ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun n ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (361))
           (Prims.of_int (15)) (Prims.of_int (361)) (Prims.of_int (49)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (361))
           (Prims.of_int (4)) (Prims.of_int (361)) (Prims.of_int (51)))
        (Obj.magic
           (FStar_Tactics_Util.repeatn n
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 -> FStar_Reflection_Data.Q_Explicit)))
                   uu___)))
        (fun uu___ -> (fun uu___ -> Obj.magic (exact_args uu___ t)) uu___)
let (ngoals : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (364))
         (Prims.of_int (47)) (Prims.of_int (364)) (Prims.of_int (57)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (364))
         (Prims.of_int (26)) (Prims.of_int (364)) (Prims.of_int (57)))
      (Obj.magic (goals ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_List_Tot_Base.length uu___1))
let (ngoals_smt : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (367))
         (Prims.of_int (51)) (Prims.of_int (367)) (Prims.of_int (65)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (367))
         (Prims.of_int (30)) (Prims.of_int (367)) (Prims.of_int (65)))
      (Obj.magic (smt_goals ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_List_Tot_Base.length uu___1))
let (fresh_bv :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (375))
         (Prims.of_int (12)) (Prims.of_int (375)) (Prims.of_int (20)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (376))
         (Prims.of_int (4)) (Prims.of_int (376)) (Prims.of_int (44)))
      (Obj.magic (FStar_Tactics_Builtins.fresh ()))
      (fun uu___ ->
         (fun i ->
            Obj.magic
              (FStar_Tactics_Builtins.fresh_bv_named
                 (Prims.strcat "x" (Prims.string_of_int i)) t)) uu___)
let (fresh_binder_named :
  Prims.string ->
    FStar_Reflection_Types.typ ->
      (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (379))
           (Prims.of_int (14)) (Prims.of_int (379)) (Prims.of_int (35)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (379))
           (Prims.of_int (4)) (Prims.of_int (379)) (Prims.of_int (35)))
        (Obj.magic (FStar_Tactics_Builtins.fresh_bv_named nm t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_Reflection_Derived.mk_binder uu___))
let (fresh_binder :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (383))
         (Prims.of_int (12)) (Prims.of_int (383)) (Prims.of_int (20)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (384))
         (Prims.of_int (4)) (Prims.of_int (384)) (Prims.of_int (48)))
      (Obj.magic (FStar_Tactics_Builtins.fresh ()))
      (fun uu___ ->
         (fun i ->
            Obj.magic
              (fresh_binder_named (Prims.strcat "x" (Prims.string_of_int i))
                 t)) uu___)
let (fresh_implicit_binder_named :
  Prims.string ->
    FStar_Reflection_Types.typ ->
      (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (387))
           (Prims.of_int (23)) (Prims.of_int (387)) (Prims.of_int (44)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (387))
           (Prims.of_int (4)) (Prims.of_int (387)) (Prims.of_int (44)))
        (Obj.magic (FStar_Tactics_Builtins.fresh_bv_named nm t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_Reflection_Derived.mk_implicit_binder uu___))
let (fresh_implicit_binder :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (391))
         (Prims.of_int (12)) (Prims.of_int (391)) (Prims.of_int (20)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (392))
         (Prims.of_int (4)) (Prims.of_int (392)) (Prims.of_int (57)))
      (Obj.magic (FStar_Tactics_Builtins.fresh ()))
      (fun uu___ ->
         (fun i ->
            Obj.magic
              (fresh_implicit_binder_named
                 (Prims.strcat "x" (Prims.string_of_int i)) t)) uu___)
let (guard : Prims.bool -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun b ->
       if Prims.op_Negation b
       then Obj.magic (Obj.repr (fail "guard failed"))
       else
         Obj.magic
           (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
      uu___
let try_with :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (Prims.exn -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun h ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (405))
           (Prims.of_int (10)) (Prims.of_int (405)) (Prims.of_int (17)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (405))
           (Prims.of_int (4)) (Prims.of_int (407)) (Prims.of_int (16)))
        (Obj.magic (FStar_Tactics_Builtins.catch f))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Inl e -> Obj.magic (Obj.repr (h e))
              | FStar_Pervasives.Inr x ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> x))))
             uu___)
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
             FStar_Tactics_Effect.tac_bind
               (Prims.mk_range "FStar.Tactics.Derived.fst"
                  (Prims.of_int (410)) (Prims.of_int (13))
                  (Prims.of_int (410)) (Prims.of_int (19)))
               (Prims.mk_range "FStar.Tactics.Derived.fst"
                  (Prims.of_int (410)) (Prims.of_int (8))
                  (Prims.of_int (410)) (Prims.of_int (19)))
               (Obj.magic (t ()))
               (fun uu___1 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___2 -> FStar_Pervasives_Native.Some uu___1)))
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
      (fun uu___ -> fail "no tactics to try") ()
let rec repeat :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (427))
         (Prims.of_int (10)) (Prims.of_int (427)) (Prims.of_int (17)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (427))
         (Prims.of_int (4)) (Prims.of_int (429)) (Prims.of_int (28)))
      (Obj.magic (FStar_Tactics_Builtins.catch t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives.Inl uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> [])))
            | FStar_Pervasives.Inr x ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (429)) (Prims.of_int (20))
                           (Prims.of_int (429)) (Prims.of_int (28)))
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (429)) (Prims.of_int (17))
                           (Prims.of_int (429)) (Prims.of_int (19)))
                        (Obj.magic (repeat t))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> x :: uu___1))))) uu___)
let repeat1 :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (432))
         (Prims.of_int (4)) (Prims.of_int (432)) (Prims.of_int (8)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (432))
         (Prims.of_int (9)) (Prims.of_int (432)) (Prims.of_int (11)))
      (Obj.magic (t ()))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (432)) (Prims.of_int (12))
                    (Prims.of_int (432)) (Prims.of_int (20)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (432)) (Prims.of_int (9))
                    (Prims.of_int (432)) (Prims.of_int (11)))
                 (Obj.magic (repeat t))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> uu___ :: uu___1)))) uu___)
let repeat' :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (435))
         (Prims.of_int (12)) (Prims.of_int (435)) (Prims.of_int (20)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (435))
         (Prims.of_int (24)) (Prims.of_int (435)) (Prims.of_int (26)))
      (Obj.magic (repeat f))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (norm_term :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (439))
           (Prims.of_int (8)) (Prims.of_int (440)) (Prims.of_int (30)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (442))
           (Prims.of_int (4)) (Prims.of_int (442)) (Prims.of_int (23)))
        (Obj.magic
           (try_with (fun uu___ -> match () with | () -> cur_env ())
              (fun uu___ -> FStar_Tactics_Builtins.top_env ())))
        (fun uu___ ->
           (fun e -> Obj.magic (FStar_Tactics_Builtins.norm_term_env e s t))
             uu___)
let (join_all_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (449))
         (Prims.of_int (16)) (Prims.of_int (449)) (Prims.of_int (38)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (449))
         (Prims.of_int (2)) (Prims.of_int (455)) (Prims.of_int (20)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (449))
               (Prims.of_int (16)) (Prims.of_int (449)) (Prims.of_int (24)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (449))
               (Prims.of_int (16)) (Prims.of_int (449)) (Prims.of_int (38)))
            (Obj.magic (goals ()))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (449)) (Prims.of_int (26))
                          (Prims.of_int (449)) (Prims.of_int (38)))
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (449)) (Prims.of_int (16))
                          (Prims.of_int (449)) (Prims.of_int (38)))
                       (Obj.magic (smt_goals ()))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> (uu___1, uu___2))))) uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (gs, sgs) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (450)) (Prims.of_int (2))
                        (Prims.of_int (450)) (Prims.of_int (18)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (451)) (Prims.of_int (2))
                        (Prims.of_int (455)) (Prims.of_int (20)))
                     (Obj.magic (FStar_Tactics_Builtins.set_smt_goals []))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (451)) (Prims.of_int (2))
                                   (Prims.of_int (451)) (Prims.of_int (15)))
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (452)) (Prims.of_int (2))
                                   (Prims.of_int (455)) (Prims.of_int (20)))
                                (Obj.magic
                                   (FStar_Tactics_Builtins.set_goals sgs))
                                (fun uu___3 ->
                                   (fun uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (452))
                                              (Prims.of_int (2))
                                              (Prims.of_int (452))
                                              (Prims.of_int (14)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (453))
                                              (Prims.of_int (2))
                                              (Prims.of_int (455))
                                              (Prims.of_int (20)))
                                           (Obj.magic
                                              (repeat'
                                                 FStar_Tactics_Builtins.join))
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (453))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (453))
                                                         (Prims.of_int (21)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (454))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (455))
                                                         (Prims.of_int (20)))
                                                      (Obj.magic (goals ()))
                                                      (fun uu___5 ->
                                                         (fun sgs' ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (14)))
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (20)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Builtins.set_goals
                                                                    gs))
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    sgs'))
                                                                    uu___5)))
                                                           uu___5))) uu___4)))
                                     uu___3))) uu___2))) uu___1)
let discard :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun tau ->
    fun uu___ ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (458))
           (Prims.of_int (22)) (Prims.of_int (458)) (Prims.of_int (28)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (458))
           (Prims.of_int (32)) (Prims.of_int (458)) (Prims.of_int (34)))
        (Obj.magic (tau ()))
        (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let rec repeatseq :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (462))
         (Prims.of_int (12)) (Prims.of_int (462)) (Prims.of_int (82)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (462))
         (Prims.of_int (86)) (Prims.of_int (462)) (Prims.of_int (88)))
      (Obj.magic
         (trytac
            (fun uu___ ->
               seq (discard t) (discard (fun uu___1 -> repeatseq t)))))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (tadmit : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Builtins.tadmit_t
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit))
let (admit1 : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> tadmit ()
let (admit_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (470))
         (Prims.of_int (12)) (Prims.of_int (470)) (Prims.of_int (25)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (471))
         (Prims.of_int (4)) (Prims.of_int (471)) (Prims.of_int (6)))
      (Obj.magic (repeat tadmit))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (is_guard : unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (475))
         (Prims.of_int (27)) (Prims.of_int (475)) (Prims.of_int (41)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (475))
         (Prims.of_int (4)) (Prims.of_int (475)) (Prims.of_int (41)))
      (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.is_guard uu___1))
let (skip_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (478))
         (Prims.of_int (7)) (Prims.of_int (478)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (478))
         (Prims.of_int (4)) (Prims.of_int (480)) (Prims.of_int (16)))
      (Obj.magic (is_guard ()))
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1 then Obj.magic (smt ()) else Obj.magic (fail ""))
           uu___1)
let (guards_to_smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (483))
         (Prims.of_int (12)) (Prims.of_int (483)) (Prims.of_int (29)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (484))
         (Prims.of_int (4)) (Prims.of_int (484)) (Prims.of_int (6)))
      (Obj.magic (repeat skip_guard))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (simpl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.simplify; FStar_Pervasives.primops]
let (whnf : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.weak;
      FStar_Pervasives.hnf;
      FStar_Pervasives.primops;
      FStar_Pervasives.delta]
let (compute : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.primops;
      FStar_Pervasives.iota;
      FStar_Pervasives.delta;
      FStar_Pervasives.zeta]
let (intros :
  unit ->
    (FStar_Reflection_Types.binder Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> repeat FStar_Tactics_Builtins.intro
let (intros' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (492))
         (Prims.of_int (36)) (Prims.of_int (492)) (Prims.of_int (45)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (492))
         (Prims.of_int (49)) (Prims.of_int (492)) (Prims.of_int (51)))
      (Obj.magic (intros ()))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (destruct :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (493))
         (Prims.of_int (37)) (Prims.of_int (493)) (Prims.of_int (50)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (493))
         (Prims.of_int (54)) (Prims.of_int (493)) (Prims.of_int (56)))
      (Obj.magic (FStar_Tactics_Builtins.t_destruct tm))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (destruct_intros :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    seq
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (494))
              (Prims.of_int (59)) (Prims.of_int (494)) (Prims.of_int (72)))
           (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (494))
              (Prims.of_int (76)) (Prims.of_int (494)) (Prims.of_int (78)))
           (Obj.magic (FStar_Tactics_Builtins.t_destruct tm))
           (fun uu___1 ->
              FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) intros'
let __cut : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
let (tcut :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (500))
         (Prims.of_int (12)) (Prims.of_int (500)) (Prims.of_int (23)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (501))
         (Prims.of_int (4)) (Prims.of_int (503)) (Prims.of_int (12)))
      (Obj.magic (cur_goal ()))
      (fun uu___ ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (501)) (Prims.of_int (13))
                    (Prims.of_int (501)) (Prims.of_int (37)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (502)) (Prims.of_int (4))
                    (Prims.of_int (503)) (Prims.of_int (12)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_Reflection_Derived.mk_e_app
                         (FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_FVar
                               (FStar_Reflection_Builtins.pack_fv
                                  ["FStar"; "Tactics"; "Derived"; "__cut"])))
                         [t; g]))
                 (fun uu___ ->
                    (fun tt ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (502)) (Prims.of_int (4))
                               (Prims.of_int (502)) (Prims.of_int (12)))
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (503)) (Prims.of_int (4))
                               (Prims.of_int (503)) (Prims.of_int (12)))
                            (Obj.magic (apply tt))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic (FStar_Tactics_Builtins.intro ()))
                                 uu___))) uu___))) uu___)
let (pose :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (506))
         (Prims.of_int (4)) (Prims.of_int (506)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (507))
         (Prims.of_int (4)) (Prims.of_int (509)) (Prims.of_int (12)))
      (Obj.magic
         (apply
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Derived"; "__cut"])))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (507)) (Prims.of_int (4))
                    (Prims.of_int (507)) (Prims.of_int (11)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (508)) (Prims.of_int (4))
                    (Prims.of_int (509)) (Prims.of_int (12)))
                 (Obj.magic (flip ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (508)) (Prims.of_int (4))
                               (Prims.of_int (508)) (Prims.of_int (11)))
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (509)) (Prims.of_int (4))
                               (Prims.of_int (509)) (Prims.of_int (12)))
                            (Obj.magic (exact t))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  Obj.magic (FStar_Tactics_Builtins.intro ()))
                                 uu___2))) uu___1))) uu___)
let (intro_as :
  Prims.string ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (512))
         (Prims.of_int (12)) (Prims.of_int (512)) (Prims.of_int (20)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (513))
         (Prims.of_int (4)) (Prims.of_int (513)) (Prims.of_int (17)))
      (Obj.magic (FStar_Tactics_Builtins.intro ()))
      (fun uu___ ->
         (fun b -> Obj.magic (FStar_Tactics_Builtins.rename_to b s)) uu___)
let (pose_as :
  Prims.string ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (516))
           (Prims.of_int (12)) (Prims.of_int (516)) (Prims.of_int (18)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (517))
           (Prims.of_int (4)) (Prims.of_int (517)) (Prims.of_int (17)))
        (Obj.magic (pose t))
        (fun uu___ ->
           (fun b -> Obj.magic (FStar_Tactics_Builtins.rename_to b s)) uu___)
let for_each_binder :
  'a .
    (FStar_Reflection_Types.binder ->
       ('a, unit) FStar_Tactics_Effect.tac_repr)
      -> ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (520))
         (Prims.of_int (10)) (Prims.of_int (520)) (Prims.of_int (26)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (520))
         (Prims.of_int (4)) (Prims.of_int (520)) (Prims.of_int (26)))
      (Obj.magic (cur_binders ()))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Util.map f uu___)) uu___)
let rec (revert_all :
  FStar_Reflection_Types.binders ->
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
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (525)) (Prims.of_int (15))
                      (Prims.of_int (525)) (Prims.of_int (24)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (526)) (Prims.of_int (15))
                      (Prims.of_int (526)) (Prims.of_int (28)))
                   (Obj.magic (FStar_Tactics_Builtins.revert ()))
                   (fun uu___1 ->
                      (fun uu___1 -> Obj.magic (revert_all tl)) uu___1))))
      uu___
let (bv_to_term :
  FStar_Reflection_Types.bv ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun bv -> FStar_Tactics_Builtins.pack (FStar_Reflection_Data.Tv_Var bv)
let (binder_to_term :
  FStar_Reflection_Types.binder ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (530))
         (Prims.of_int (57)) (Prims.of_int (530)) (Prims.of_int (73)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (530))
         (Prims.of_int (45)) (Prims.of_int (530)) (Prims.of_int (90)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_binder b))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with | (bv, uu___1) -> Obj.magic (bv_to_term bv))
           uu___)
let rec (__assumption_aux :
  FStar_Reflection_Types.binders ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    match bs with
    | [] -> fail "no assumption matches goal"
    | b::bs1 ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (539))
             (Prims.of_int (16)) (Prims.of_int (539)) (Prims.of_int (32)))
          (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (540))
             (Prims.of_int (8)) (Prims.of_int (543)) (Prims.of_int (27)))
          (Obj.magic (binder_to_term b))
          (fun uu___ ->
             (fun t ->
                Obj.magic
                  (try_with (fun uu___ -> match () with | () -> exact t)
                     (fun uu___ ->
                        try_with
                          (fun uu___1 ->
                             match () with
                             | () ->
                                 FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (541))
                                      (Prims.of_int (13))
                                      (Prims.of_int (541))
                                      (Prims.of_int (48)))
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (542))
                                      (Prims.of_int (13))
                                      (Prims.of_int (542))
                                      (Prims.of_int (20)))
                                   (Obj.magic
                                      (apply
                                         (FStar_Reflection_Builtins.pack_ln
                                            (FStar_Reflection_Data.Tv_FVar
                                               (FStar_Reflection_Builtins.pack_fv
                                                  ["FStar";
                                                  "Squash";
                                                  "return_squash"])))))
                                   (fun uu___2 ->
                                      (fun uu___2 -> Obj.magic (exact t))
                                        uu___2))
                          (fun uu___1 -> __assumption_aux bs1)))) uu___)
let (assumption : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (546))
         (Prims.of_int (21)) (Prims.of_int (546)) (Prims.of_int (37)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (546))
         (Prims.of_int (4)) (Prims.of_int (546)) (Prims.of_int (37)))
      (Obj.magic (cur_binders ()))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (__assumption_aux uu___1)) uu___1)
let (destruct_equality_implication :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Formula.formula * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (549))
         (Prims.of_int (10)) (Prims.of_int (549)) (Prims.of_int (27)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (549))
         (Prims.of_int (4)) (Prims.of_int (556)) (Prims.of_int (15)))
      (Obj.magic (FStar_Reflection_Formula.term_as_formula t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Formula.Implies (lhs, rhs) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (551)) (Prims.of_int (18))
                           (Prims.of_int (551)) (Prims.of_int (38)))
                        (Prims.mk_range "FStar.Tactics.Derived.fst"
                           (Prims.of_int (552)) (Prims.of_int (14))
                           (Prims.of_int (554)) (Prims.of_int (19)))
                        (Obj.magic
                           (FStar_Reflection_Formula.term_as_formula' lhs))
                        (fun lhs1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                match lhs1 with
                                | FStar_Reflection_Formula.Comp
                                    (FStar_Reflection_Formula.Eq uu___2,
                                     uu___3, uu___4)
                                    ->
                                    FStar_Pervasives_Native.Some (lhs1, rhs)
                                | uu___2 -> FStar_Pervasives_Native.None))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pervasives_Native.None)))) uu___)
let (rewrite' :
  FStar_Reflection_Types.binder -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    op_Less_Bar_Greater
      (op_Less_Bar_Greater (fun uu___ -> FStar_Tactics_Builtins.rewrite b)
         (fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.Tactics.Derived.fst"
                 (Prims.of_int (565)) (Prims.of_int (20))
                 (Prims.of_int (565)) (Prims.of_int (35)))
              (Prims.mk_range "FStar.Tactics.Derived.fst"
                 (Prims.of_int (566)) (Prims.of_int (20))
                 (Prims.of_int (567)) (Prims.of_int (29)))
              (Obj.magic (FStar_Tactics_Builtins.binder_retype b))
              (fun uu___1 ->
                 (fun uu___1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (566)) (Prims.of_int (20))
                            (Prims.of_int (566)) (Prims.of_int (43)))
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (567)) (Prims.of_int (20))
                            (Prims.of_int (567)) (Prims.of_int (29)))
                         (Obj.magic
                            (apply_lemma
                               (FStar_Reflection_Builtins.pack_ln
                                  (FStar_Reflection_Data.Tv_FVar
                                     (FStar_Reflection_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Derived";
                                        "__eq_sym"])))))
                         (fun uu___2 ->
                            (fun uu___2 ->
                               Obj.magic (FStar_Tactics_Builtins.rewrite b))
                              uu___2))) uu___1)))
      (fun uu___ -> fail "rewrite' failed") ()
let rec (try_rewrite_equality :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.binders ->
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
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (575)) (Prims.of_int (20))
                          (Prims.of_int (575)) (Prims.of_int (56)))
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (575)) (Prims.of_int (14))
                          (Prims.of_int (581)) (Prims.of_int (37)))
                       (Obj.magic
                          (FStar_Reflection_Formula.term_as_formula
                             (FStar_Reflection_Derived.type_of_binder x_t)))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | FStar_Reflection_Formula.Comp
                                 (FStar_Reflection_Formula.Eq uu___1, y,
                                  uu___2)
                                 ->
                                 if FStar_Reflection_Builtins.term_eq x y
                                 then
                                   Obj.magic
                                     (FStar_Tactics_Builtins.rewrite x_t)
                                 else Obj.magic (try_rewrite_equality x bs1)
                             | uu___1 ->
                                 Obj.magic (try_rewrite_equality x bs1))
                            uu___)))) uu___1 uu___
let rec (rewrite_all_context_equalities :
  FStar_Reflection_Types.binders ->
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
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (588)) (Prims.of_int (8))
                      (Prims.of_int (588)) (Prims.of_int (40)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (589)) (Prims.of_int (8))
                      (Prims.of_int (589)) (Prims.of_int (41)))
                   (Obj.magic
                      (try_with
                         (fun uu___ ->
                            match () with
                            | () -> FStar_Tactics_Builtins.rewrite x_t)
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> ()))) uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic (rewrite_all_context_equalities bs1))
                        uu___)))) uu___
let (rewrite_eqs_from_context :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (593))
         (Prims.of_int (35)) (Prims.of_int (593)) (Prims.of_int (51)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (593))
         (Prims.of_int (4)) (Prims.of_int (593)) (Prims.of_int (51)))
      (Obj.magic (cur_binders ()))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (rewrite_all_context_equalities uu___1))
           uu___1)
let (rewrite_equality :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (596))
         (Prims.of_int (27)) (Prims.of_int (596)) (Prims.of_int (43)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (596))
         (Prims.of_int (4)) (Prims.of_int (596)) (Prims.of_int (43)))
      (Obj.magic (cur_binders ()))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (try_rewrite_equality t uu___)) uu___)
let (unfold_def :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (599))
         (Prims.of_int (10)) (Prims.of_int (599)) (Prims.of_int (19)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (599))
         (Prims.of_int (4)) (Prims.of_int (603)) (Prims.of_int (46)))
      (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_FVar fv ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (601)) (Prims.of_int (16))
                        (Prims.of_int (601)) (Prims.of_int (42)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (602)) (Prims.of_int (8))
                        (Prims.of_int (602)) (Prims.of_int (30)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Reflection_Builtins.implode_qn
                             (FStar_Reflection_Builtins.inspect_fv fv)))
                     (fun uu___1 ->
                        (fun n ->
                           Obj.magic
                             (FStar_Tactics_Builtins.norm
                                [FStar_Pervasives.delta_fully [n]])) uu___1))
            | uu___1 -> Obj.magic (fail "unfold_def: term is not a fv"))
           uu___)
let (l_to_r :
  FStar_Reflection_Types.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lems ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (610))
         (Prims.of_int (8)) (Prims.of_int (613)) (Prims.of_int (31)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (614))
         (Prims.of_int (4)) (Prims.of_int (614)) (Prims.of_int (28)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun uu___1 ->
              FStar_Tactics_Effect.tac_bind
                (Prims.mk_range "FStar.Tactics.Derived.fst"
                   (Prims.of_int (610)) (Prims.of_int (8))
                   (Prims.of_int (613)) (Prims.of_int (31)))
                (Prims.mk_range "FStar.Tactics.Derived.fst"
                   (Prims.of_int (610)) (Prims.of_int (8))
                   (Prims.of_int (613)) (Prims.of_int (31)))
                (Obj.magic
                   (FStar_Tactics_Util.fold_left
                      (fun uu___3 ->
                         fun uu___2 ->
                           (fun k ->
                              fun l ->
                                Obj.magic
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        fun uu___3 ->
                                          or_else
                                            (fun uu___4 -> apply_lemma_rw l)
                                            k))) uu___3 uu___2) trefl lems))
                (fun uu___2 -> (fun uu___2 -> Obj.magic (uu___2 ())) uu___2)))
      (fun uu___ ->
         (fun first_or_trefl -> Obj.magic (pointwise first_or_trefl)) uu___)
let (mk_squash : FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t ->
    let sq =
      FStar_Reflection_Builtins.pack_ln
        (FStar_Reflection_Data.Tv_FVar
           (FStar_Reflection_Builtins.pack_fv
              FStar_Reflection_Const.squash_qn)) in
    FStar_Reflection_Derived.mk_e_app sq [t]
let (mk_sq_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      let eq =
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn)) in
      mk_squash (FStar_Reflection_Derived.mk_e_app eq [t1; t2])
let (grewrite :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (627))
           (Prims.of_int (12)) (Prims.of_int (627)) (Prims.of_int (33)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (628))
           (Prims.of_int (4)) (Prims.of_int (641)) (Prims.of_int (44)))
        (Obj.magic (tcut (mk_sq_eq t1 t2)))
        (fun uu___ ->
           (fun e ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (628)) (Prims.of_int (12))
                      (Prims.of_int (628)) (Prims.of_int (45)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (629)) (Prims.of_int (4))
                      (Prims.of_int (641)) (Prims.of_int (44)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         FStar_Reflection_Builtins.pack_ln
                           (FStar_Reflection_Data.Tv_Var
                              (FStar_Reflection_Derived.bv_of_binder e))))
                   (fun uu___ ->
                      (fun e1 ->
                         Obj.magic
                           (pointwise
                              (fun uu___ ->
                                 FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (632)) (Prims.of_int (8))
                                      (Prims.of_int (637))
                                      (Prims.of_int (20)))
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (639)) (Prims.of_int (6))
                                      (Prims.of_int (641))
                                      (Prims.of_int (43)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (632))
                                            (Prims.of_int (14))
                                            (Prims.of_int (632))
                                            (Prims.of_int (42)))
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (632))
                                            (Prims.of_int (8))
                                            (Prims.of_int (637))
                                            (Prims.of_int (20)))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (632))
                                                  (Prims.of_int (30))
                                                  (Prims.of_int (632))
                                                  (Prims.of_int (42)))
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (632))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (632))
                                                  (Prims.of_int (42)))
                                               (Obj.magic (cur_goal ()))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     Obj.magic
                                                       (FStar_Reflection_Formula.term_as_formula
                                                          uu___1)) uu___1)))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 match uu___1 with
                                                 | FStar_Reflection_Formula.Comp
                                                     (FStar_Reflection_Formula.Eq
                                                      uu___3, lhs, rhs)
                                                     ->
                                                     (match FStar_Reflection_Builtins.inspect_ln
                                                              lhs
                                                      with
                                                      | FStar_Reflection_Data.Tv_Uvar
                                                          (uu___4, uu___5) ->
                                                          true
                                                      | uu___4 -> false)
                                                 | uu___3 -> false))))
                                   (fun uu___1 ->
                                      (fun is_uvar ->
                                         if is_uvar
                                         then Obj.magic (trefl ())
                                         else
                                           Obj.magic
                                             (try_with
                                                (fun uu___2 ->
                                                   match () with
                                                   | () -> exact e1)
                                                (fun uu___2 -> trefl ())))
                                        uu___1)))) uu___))) uu___)
let (grewrite_eq :
  FStar_Reflection_Types.binder -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (648))
         (Prims.of_int (8)) (Prims.of_int (648)) (Prims.of_int (42)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (648))
         (Prims.of_int (2)) (Prims.of_int (660)) (Prims.of_int (7)))
      (Obj.magic
         (FStar_Reflection_Formula.term_as_formula
            (FStar_Reflection_Derived.type_of_binder b)))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Formula.Comp
                (FStar_Reflection_Formula.Eq uu___1, l, r) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (650)) (Prims.of_int (4))
                        (Prims.of_int (650)) (Prims.of_int (16)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (651)) (Prims.of_int (4))
                        (Prims.of_int (651)) (Prims.of_int (54)))
                     (Obj.magic (grewrite l r))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (iseq
                                [idtac;
                                (fun uu___3 ->
                                   FStar_Tactics_Effect.tac_bind
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (651))
                                        (Prims.of_int (34))
                                        (Prims.of_int (651))
                                        (Prims.of_int (52)))
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (651))
                                        (Prims.of_int (28))
                                        (Prims.of_int (651))
                                        (Prims.of_int (52)))
                                     (Obj.magic (binder_to_term b))
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           Obj.magic (exact uu___4)) uu___4))]))
                          uu___2))
            | uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (653)) (Prims.of_int (16))
                        (Prims.of_int (653)) (Prims.of_int (51)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (653)) (Prims.of_int (10))
                        (Prims.of_int (659)) (Prims.of_int (56)))
                     (Obj.magic
                        (FStar_Reflection_Formula.term_as_formula'
                           (FStar_Reflection_Derived.type_of_binder b)))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           match uu___2 with
                           | FStar_Reflection_Formula.Comp
                               (FStar_Reflection_Formula.Eq uu___3, l, r) ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (655))
                                       (Prims.of_int (6))
                                       (Prims.of_int (655))
                                       (Prims.of_int (18)))
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (656))
                                       (Prims.of_int (6))
                                       (Prims.of_int (657))
                                       (Prims.of_int (56)))
                                    (Obj.magic (grewrite l r))
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          Obj.magic
                                            (iseq
                                               [idtac;
                                               (fun uu___5 ->
                                                  FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Derived.fst"
                                                       (Prims.of_int (656))
                                                       (Prims.of_int (30))
                                                       (Prims.of_int (656))
                                                       (Prims.of_int (55)))
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Derived.fst"
                                                       (Prims.of_int (657))
                                                       (Prims.of_int (30))
                                                       (Prims.of_int (657))
                                                       (Prims.of_int (54)))
                                                    (Obj.magic
                                                       (apply_lemma
                                                          (FStar_Reflection_Builtins.pack_ln
                                                             (FStar_Reflection_Data.Tv_FVar
                                                                (FStar_Reflection_Builtins.pack_fv
                                                                   ["FStar";
                                                                   "Tactics";
                                                                   "Derived";
                                                                   "__un_sq_eq"])))))
                                                    (fun uu___6 ->
                                                       (fun uu___6 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (657))
                                                                  (Prims.of_int (36))
                                                                  (Prims.of_int (657))
                                                                  (Prims.of_int (54)))
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (657))
                                                                  (Prims.of_int (30))
                                                                  (Prims.of_int (657))
                                                                  (Prims.of_int (54)))
                                                               (Obj.magic
                                                                  (binder_to_term
                                                                    b))
                                                               (fun uu___7 ->
                                                                  (fun uu___7
                                                                    ->
                                                                    Obj.magic
                                                                    (exact
                                                                    uu___7))
                                                                    uu___7)))
                                                         uu___6))])) uu___4))
                           | uu___3 ->
                               Obj.magic
                                 (fail
                                    "grewrite_eq: binder type is not an equality"))
                          uu___2))) uu___)
let rec (apply_squash_or_lem :
  Prims.nat ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun t ->
      try_with (fun uu___ -> match () with | () -> apply t)
        (fun uu___ ->
           try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_Effect.tac_bind
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (682)) (Prims.of_int (8))
                         (Prims.of_int (682)) (Prims.of_int (43)))
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (682)) (Prims.of_int (45))
                         (Prims.of_int (682)) (Prims.of_int (52)))
                      (Obj.magic
                         (apply
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar"; "Squash"; "return_squash"])))))
                      (fun uu___2 ->
                         (fun uu___2 -> Obj.magic (apply t)) uu___2))
             (fun uu___1 ->
                try_with (fun uu___2 -> match () with | () -> apply_lemma t)
                  (fun uu___2 ->
                     if d <= Prims.int_zero
                     then fail "mapply: out of fuel"
                     else
                       FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (688)) (Prims.of_int (13))
                            (Prims.of_int (688)) (Prims.of_int (30)))
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (689)) (Prims.of_int (4))
                            (Prims.of_int (737)) (Prims.of_int (41)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (688)) (Prims.of_int (16))
                                  (Prims.of_int (688)) (Prims.of_int (28)))
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (688)) (Prims.of_int (13))
                                  (Prims.of_int (688)) (Prims.of_int (30)))
                               (Obj.magic (cur_env ()))
                               (fun uu___4 ->
                                  (fun uu___4 ->
                                     Obj.magic
                                       (FStar_Tactics_Builtins.tc uu___4 t))
                                    uu___4)))
                         (fun uu___4 ->
                            (fun ty ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (689))
                                       (Prims.of_int (17))
                                       (Prims.of_int (689))
                                       (Prims.of_int (31)))
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (689))
                                       (Prims.of_int (4))
                                       (Prims.of_int (737))
                                       (Prims.of_int (41)))
                                    (Obj.magic
                                       (FStar_Tactics_SyntaxHelpers.collect_arr
                                          ty))
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          match uu___4 with
                                          | (tys, c) ->
                                              (match FStar_Reflection_Builtins.inspect_comp
                                                       c
                                               with
                                               | FStar_Reflection_Data.C_Lemma
                                                   (pre, post, uu___5) ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (693))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (693))
                                                           (Prims.of_int (32)))
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (694))
                                                           (Prims.of_int (7))
                                                           (Prims.of_int (702))
                                                           (Prims.of_int (41)))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              FStar_Reflection_Builtins.pack_ln
                                                                (FStar_Reflection_Data.Tv_App
                                                                   (post,
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                        (fun uu___6 ->
                                                           (fun post1 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (35)))
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (41)))
                                                                   (Obj.magic
                                                                    (norm_term
                                                                    [] post1))
                                                                   (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (41)))
                                                                    (Obj.magic
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    post2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (31)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"])))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___7))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (fail
                                                                    "mapply: can't apply (1)"))
                                                                    uu___6)))
                                                                    uu___6)))
                                                             uu___6))
                                               | FStar_Reflection_Data.C_Total
                                                   rt ->
                                                   (match FStar_Reflection_Derived.unsquash_term
                                                            rt
                                                    with
                                                    | FStar_Pervasives_Native.Some
                                                        rt1 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (710))
                                                                (Prims.of_int (18))
                                                                (Prims.of_int (710))
                                                                (Prims.of_int (33)))
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (712))
                                                                (Prims.of_int (9))
                                                                (Prims.of_int (718))
                                                                (Prims.of_int (43)))
                                                             (Obj.magic
                                                                (norm_term []
                                                                   rt1))
                                                             (fun uu___5 ->
                                                                (fun rt2 ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    rt2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (33)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___6))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (fail
                                                                    "mapply: can't apply (1)"))
                                                                    uu___5)))
                                                                  uu___5))
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (725))
                                                                (Prims.of_int (18))
                                                                (Prims.of_int (725))
                                                                (Prims.of_int (33)))
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (727))
                                                                (Prims.of_int (9))
                                                                (Prims.of_int (734))
                                                                (Prims.of_int (20)))
                                                             (Obj.magic
                                                                (norm_term []
                                                                   rt))
                                                             (fun uu___5 ->
                                                                (fun rt1 ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    rt1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (33)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___6))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (48)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Squash";
                                                                    "return_squash"])))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (apply t))
                                                                    uu___7)))
                                                                    uu___5)))
                                                                  uu___5)))
                                               | uu___5 ->
                                                   Obj.magic
                                                     (fail
                                                        "mapply: can't apply (2)")))
                                         uu___4))) uu___4))))
let (mapply :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> apply_squash_or_lem (Prims.of_int (10)) t
let (admit_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (747))
         (Prims.of_int (2)) (Prims.of_int (747)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (748))
         (Prims.of_int (2)) (Prims.of_int (748)) (Prims.of_int (16)))
      (Obj.magic (FStar_Tactics_Builtins.dump "Admitting"))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (apply
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_FVar
                       (FStar_Reflection_Builtins.pack_fv ["Prims"; "admit"])))))
           uu___1)
let admit_dump : 'a . (unit -> 'a) -> unit -> 'a = fun x -> fun uu___ -> x ()
let (magic_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (755))
         (Prims.of_int (2)) (Prims.of_int (755)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (756))
         (Prims.of_int (2)) (Prims.of_int (758)) (Prims.of_int (4)))
      (Obj.magic (FStar_Tactics_Builtins.dump "Admitting"))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (756)) (Prims.of_int (2))
                    (Prims.of_int (756)) (Prims.of_int (16)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (757)) (Prims.of_int (2))
                    (Prims.of_int (758)) (Prims.of_int (4)))
                 (Obj.magic
                    (apply
                       (FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_FVar
                             (FStar_Reflection_Builtins.pack_fv
                                ["Prims"; "magic"])))))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (757)) (Prims.of_int (2))
                               (Prims.of_int (757)) (Prims.of_int (13)))
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (758)) (Prims.of_int (2))
                               (Prims.of_int (758)) (Prims.of_int (4)))
                            (Obj.magic
                               (exact
                                  (FStar_Reflection_Builtins.pack_ln
                                     (FStar_Reflection_Data.Tv_Const
                                        FStar_Reflection_Data.C_Unit))))
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> ())))) uu___2))) uu___1)
let magic_dump : 'a . 'a -> unit -> 'a = fun x -> fun uu___ -> x
let (change_with :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      focus
        (fun uu___ ->
           FStar_Tactics_Effect.tac_bind
             (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (765))
                (Prims.of_int (8)) (Prims.of_int (765)) (Prims.of_int (22)))
             (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (766))
                (Prims.of_int (8)) (Prims.of_int (766)) (Prims.of_int (29)))
             (Obj.magic (grewrite t1 t2))
             (fun uu___1 ->
                (fun uu___1 -> Obj.magic (iseq [idtac; trivial])) uu___1))
let (change_sq :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    FStar_Tactics_Builtins.change
      (FStar_Reflection_Derived.mk_e_app
         (FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv ["Prims"; "squash"]))) 
         [t1])
let finish_by :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (773))
         (Prims.of_int (12)) (Prims.of_int (773)) (Prims.of_int (16)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (774))
         (Prims.of_int (4)) (Prims.of_int (775)) (Prims.of_int (5)))
      (Obj.magic (t ()))
      (fun uu___ ->
         (fun x ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (774)) (Prims.of_int (4))
                    (Prims.of_int (774)) (Prims.of_int (58)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (773)) (Prims.of_int (8))
                    (Prims.of_int (773)) (Prims.of_int (9)))
                 (Obj.magic
                    (or_else qed
                       (fun uu___ -> fail "finish_by: not finished")))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> x))))
           uu___)
let solve_then :
  'a 'b .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
        ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (778))
           (Prims.of_int (4)) (Prims.of_int (778)) (Prims.of_int (10)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (779))
           (Prims.of_int (4)) (Prims.of_int (782)) (Prims.of_int (5)))
        (Obj.magic (FStar_Tactics_Builtins.dup ()))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (779)) (Prims.of_int (12))
                      (Prims.of_int (779)) (Prims.of_int (42)))
                   (Prims.mk_range "FStar.Tactics.Derived.fst"
                      (Prims.of_int (780)) (Prims.of_int (4))
                      (Prims.of_int (782)) (Prims.of_int (5)))
                   (Obj.magic (focus (fun uu___1 -> finish_by t1)))
                   (fun uu___1 ->
                      (fun x ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (780)) (Prims.of_int (12))
                                 (Prims.of_int (780)) (Prims.of_int (16)))
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (781)) (Prims.of_int (4))
                                 (Prims.of_int (782)) (Prims.of_int (5)))
                              (Obj.magic (t2 x))
                              (fun uu___1 ->
                                 (fun y ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (781))
                                            (Prims.of_int (4))
                                            (Prims.of_int (781))
                                            (Prims.of_int (12)))
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (780))
                                            (Prims.of_int (8))
                                            (Prims.of_int (780))
                                            (Prims.of_int (9)))
                                         (Obj.magic (trefl ()))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 -> y)))) uu___1)))
                        uu___1))) uu___)
let add_elem :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    focus
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (785))
              (Prims.of_int (4)) (Prims.of_int (785)) (Prims.of_int (17)))
           (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (786))
              (Prims.of_int (4)) (Prims.of_int (790)) (Prims.of_int (5)))
           (Obj.magic
              (apply
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_FVar
                       (FStar_Reflection_Builtins.pack_fv ["Prims"; "Cons"])))))
           (fun uu___1 ->
              (fun uu___1 ->
                 Obj.magic
                   (focus
                      (fun uu___2 ->
                         FStar_Tactics_Effect.tac_bind
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (787)) (Prims.of_int (14))
                              (Prims.of_int (787)) (Prims.of_int (18)))
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (788)) (Prims.of_int (6))
                              (Prims.of_int (789)) (Prims.of_int (7)))
                           (Obj.magic (t ()))
                           (fun uu___3 ->
                              (fun x ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (788))
                                         (Prims.of_int (6))
                                         (Prims.of_int (788))
                                         (Prims.of_int (12)))
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (787))
                                         (Prims.of_int (10))
                                         (Prims.of_int (787))
                                         (Prims.of_int (11)))
                                      (Obj.magic (qed ()))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> x)))) uu___3))))
                uu___1))
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
             FStar_Tactics_Effect.tac_bind
               (Prims.mk_range "FStar.Tactics.Derived.fst"
                  (Prims.of_int (809)) (Prims.of_int (42))
                  (Prims.of_int (809)) (Prims.of_int (51)))
               (Prims.mk_range "FStar.Tactics.Derived.fst"
                  (Prims.of_int (809)) (Prims.of_int (36))
                  (Prims.of_int (809)) (Prims.of_int (51)))
               (FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 ->
                     (fun uu___2 ->
                        Obj.magic
                          (failwith
                             "Cannot evaluate open quotation at runtime"))
                       uu___2))
               (fun uu___2 -> (fun uu___2 -> Obj.magic (exact uu___2)) uu___2))
          (fun uu___1 ->
             FStar_Tactics_Builtins.norm
               [FStar_Pervasives.delta_only l;
               FStar_Pervasives.iota;
               FStar_Pervasives.zeta])
let (tlabel : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (812))
         (Prims.of_int (10)) (Prims.of_int (812)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (812))
         (Prims.of_int (4)) (Prims.of_int (815)) (Prims.of_int (38)))
      (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] -> Obj.magic (fail "tlabel: no goals")
            | h::t ->
                Obj.magic
                  (FStar_Tactics_Builtins.set_goals
                     ((FStar_Tactics_Types.set_label l h) :: t))) uu___)
let (tlabel' : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (818))
         (Prims.of_int (10)) (Prims.of_int (818)) (Prims.of_int (18)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (818))
         (Prims.of_int (4)) (Prims.of_int (822)) (Prims.of_int (26)))
      (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] -> Obj.magic (fail "tlabel': no goals")
            | h::t ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (821)) (Prims.of_int (16))
                        (Prims.of_int (821)) (Prims.of_int (45)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (822)) (Prims.of_int (8))
                        (Prims.of_int (822)) (Prims.of_int (26)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Tactics_Types.set_label
                             (Prims.strcat l
                                (FStar_Tactics_Types.get_label h)) h))
                     (fun uu___1 ->
                        (fun h1 ->
                           Obj.magic
                             (FStar_Tactics_Builtins.set_goals (h1 :: t)))
                          uu___1))) uu___)
let (focus_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (825))
         (Prims.of_int (4)) (Prims.of_int (825)) (Prims.of_int (39)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (826))
         (Prims.of_int (4)) (Prims.of_int (826)) (Prims.of_int (20)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (825))
               (Prims.of_int (14)) (Prims.of_int (825)) (Prims.of_int (39)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (825))
               (Prims.of_int (4)) (Prims.of_int (825)) (Prims.of_int (39)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                     (Prims.of_int (825)) (Prims.of_int (15))
                     (Prims.of_int (825)) (Prims.of_int (23)))
                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                     (Prims.of_int (825)) (Prims.of_int (14))
                     (Prims.of_int (825)) (Prims.of_int (39)))
                  (Obj.magic (goals ()))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (825)) (Prims.of_int (26))
                                (Prims.of_int (825)) (Prims.of_int (38)))
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (825)) (Prims.of_int (14))
                                (Prims.of_int (825)) (Prims.of_int (39)))
                             (Obj.magic (smt_goals ()))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     FStar_List_Tot_Base.op_At uu___1 uu___2))))
                       uu___1)))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic (FStar_Tactics_Builtins.set_goals uu___1)) uu___1)))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_Builtins.set_smt_goals []))
           uu___1)
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
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (841))
         (Prims.of_int (8)) (Prims.of_int (841)) (Prims.of_int (38)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (841))
         (Prims.of_int (2)) (Prims.of_int (843)) (Prims.of_int (37)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (841))
               (Prims.of_int (28)) (Prims.of_int (841)) (Prims.of_int (38)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (841))
               (Prims.of_int (8)) (Prims.of_int (841)) (Prims.of_int (38)))
            (Obj.magic (goals ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> extract_nth (n - Prims.int_one) uu___))))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives_Native.None ->
                Obj.magic (fail "bump_nth: not that many goals")
            | FStar_Pervasives_Native.Some (h, t) ->
                Obj.magic (FStar_Tactics_Builtins.set_goals (h :: t))) uu___)
let rec (destruct_list :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (846))
         (Prims.of_int (21)) (Prims.of_int (846)) (Prims.of_int (34)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (846))
         (Prims.of_int (4)) (Prims.of_int (858)) (Prims.of_int (27)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Derived.collect_app t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (head, args) ->
                (match ((FStar_Reflection_Builtins.inspect_ln head), args)
                 with
                 | (FStar_Reflection_Data.Tv_FVar fv,
                    (a1, FStar_Reflection_Data.Q_Explicit)::(a2,
                                                             FStar_Reflection_Data.Q_Explicit)::[])
                     ->
                     Obj.magic
                       (Obj.repr
                          (if
                             (FStar_Reflection_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.cons_qn
                           then
                             FStar_Tactics_Effect.tac_bind
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (851)) (Prims.of_int (17))
                                  (Prims.of_int (851)) (Prims.of_int (33)))
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (851)) (Prims.of_int (14))
                                  (Prims.of_int (851)) (Prims.of_int (16)))
                               (Obj.magic (destruct_list a2))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> a1 :: uu___1))
                           else
                             FStar_Tactics_Effect.raise
                               FStar_Tactics_Common.NotAListLiteral))
                 | (FStar_Reflection_Data.Tv_FVar fv,
                    (uu___1, FStar_Reflection_Data.Q_Implicit)::(a1,
                                                                 FStar_Reflection_Data.Q_Explicit)::
                    (a2, FStar_Reflection_Data.Q_Explicit)::[]) ->
                     Obj.magic
                       (Obj.repr
                          (if
                             (FStar_Reflection_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.cons_qn
                           then
                             FStar_Tactics_Effect.tac_bind
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (851)) (Prims.of_int (17))
                                  (Prims.of_int (851)) (Prims.of_int (33)))
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (851)) (Prims.of_int (14))
                                  (Prims.of_int (851)) (Prims.of_int (16)))
                               (Obj.magic (destruct_list a2))
                               (fun uu___2 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 -> a1 :: uu___2))
                           else
                             FStar_Tactics_Effect.raise
                               FStar_Tactics_Common.NotAListLiteral))
                 | (FStar_Reflection_Data.Tv_FVar fv, uu___1) ->
                     Obj.magic
                       (Obj.repr
                          (if
                             (FStar_Reflection_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.nil_qn
                           then
                             Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> []))
                           else
                             Obj.repr
                               (FStar_Tactics_Effect.raise
                                  FStar_Tactics_Common.NotAListLiteral)))
                 | uu___1 ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.raise
                             FStar_Tactics_Common.NotAListLiteral)))) uu___)
let (get_match_body :
  unit -> (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (861))
         (Prims.of_int (8)) (Prims.of_int (861)) (Prims.of_int (35)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (861))
         (Prims.of_int (2)) (Prims.of_int (865)) (Prims.of_int (46)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (861))
               (Prims.of_int (22)) (Prims.of_int (861)) (Prims.of_int (35)))
            (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (861))
               (Prims.of_int (8)) (Prims.of_int (861)) (Prims.of_int (35)))
            (Obj.magic (cur_goal ()))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 -> FStar_Reflection_Derived.unsquash_term uu___1))))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Pervasives_Native.None -> Obj.magic (fail "")
            | FStar_Pervasives_Native.Some t ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (863)) (Prims.of_int (20))
                        (Prims.of_int (863)) (Prims.of_int (39)))
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (863)) (Prims.of_int (14))
                        (Prims.of_int (865)) (Prims.of_int (46)))
                     (Obj.magic (inspect_unascribe t))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           match uu___2 with
                           | FStar_Reflection_Data.Tv_Match
                               (sc, uu___3, uu___4) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___5 -> sc)))
                           | uu___3 ->
                               Obj.magic
                                 (Obj.repr (fail "Goal is not a match")))
                          uu___2))) uu___1)
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
         FStar_Tactics_Effect.tac_bind
           (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (878))
              (Prims.of_int (14)) (Prims.of_int (878)) (Prims.of_int (31)))
           (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (879))
              (Prims.of_int (6)) (Prims.of_int (884)) (Prims.of_int (20)))
           (Obj.magic (get_match_body ()))
           (fun uu___2 ->
              (fun x ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (879)) (Prims.of_int (14))
                         (Prims.of_int (879)) (Prims.of_int (26)))
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (880)) (Prims.of_int (6))
                         (Prims.of_int (884)) (Prims.of_int (20)))
                      (Obj.magic (FStar_Tactics_Builtins.t_destruct x))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            Obj.magic
                              (iterAll
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (881))
                                         (Prims.of_int (17))
                                         (Prims.of_int (881))
                                         (Prims.of_int (29)))
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (882))
                                         (Prims.of_int (8))
                                         (Prims.of_int (884))
                                         (Prims.of_int (19)))
                                      (Obj.magic
                                         (repeat FStar_Tactics_Builtins.intro))
                                      (fun uu___4 ->
                                         (fun bs ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (882))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (882))
                                                    (Prims.of_int (23)))
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (883))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (884))
                                                    (Prims.of_int (19)))
                                                 (Obj.magic (last bs))
                                                 (fun uu___4 ->
                                                    (fun b ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (883))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (883))
                                                               (Prims.of_int (21)))
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (884))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (884))
                                                               (Prims.of_int (19)))
                                                            (Obj.magic
                                                               (grewrite_eq b))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Builtins.norm
                                                                    [FStar_Pervasives.iota]))
                                                                 uu___4)))
                                                      uu___4))) uu___4))))
                           uu___2))) uu___2))
let (nth_binder :
  Prims.int ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun i ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (893))
         (Prims.of_int (11)) (Prims.of_int (893)) (Prims.of_int (25)))
      (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (894))
         (Prims.of_int (2)) (Prims.of_int (898)) (Prims.of_int (15)))
      (Obj.magic (cur_binders ()))
      (fun uu___ ->
         (fun bs ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (894)) (Prims.of_int (16))
                    (Prims.of_int (894)) (Prims.of_int (65)))
                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                    (Prims.of_int (895)) (Prims.of_int (2))
                    (Prims.of_int (898)) (Prims.of_int (15)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       if i >= Prims.int_zero
                       then i
                       else (FStar_List_Tot_Base.length bs) + i))
                 (fun uu___ ->
                    (fun k ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (895)) (Prims.of_int (16))
                               (Prims.of_int (895)) (Prims.of_int (62)))
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (896)) (Prims.of_int (2))
                               (Prims.of_int (898)) (Prims.of_int (15)))
                            (if k < Prims.int_zero
                             then
                               Obj.magic
                                 (Obj.repr (fail "not enough binders"))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 -> k))))
                            (fun uu___ ->
                               (fun k1 ->
                                  match FStar_List_Tot_Base.nth bs k1 with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr (fail "not enough binders"))
                                  | FStar_Pervasives_Native.Some b ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___ -> b)))) uu___)))
                      uu___))) uu___)
exception Appears 
let (uu___is_Appears : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Appears -> true | uu___ -> false
let (name_appears_in :
  FStar_Reflection_Types.name ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (906))
           (Prims.of_int (4)) (Prims.of_int (911)) (Prims.of_int (12)))
        (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (913))
           (Prims.of_int (2)) (Prims.of_int (915)) (Prims.of_int (16)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t1 ->
                FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                     (Prims.of_int (905)) (Prims.of_int (10))
                     (Prims.of_int (905)) (Prims.of_int (11)))
                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                     (Prims.of_int (906)) (Prims.of_int (4))
                     (Prims.of_int (911)) (Prims.of_int (12)))
                  (Obj.magic (FStar_Tactics_Builtins.inspect t1))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Reflection_Data.Tv_FVar fv ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (908)) (Prims.of_int (6))
                                    (Prims.of_int (909)) (Prims.of_int (21)))
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (905)) (Prims.of_int (10))
                                    (Prims.of_int (905)) (Prims.of_int (11)))
                                 (if
                                    (FStar_Reflection_Builtins.inspect_fv fv)
                                      = nm
                                  then
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.raise Appears))
                                  else
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 -> ()))))
                                 (fun uu___2 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 -> t1)))
                        | t2 -> Obj.magic (FStar_Tactics_Builtins.pack t2))
                       uu___1)))
        (fun uu___ ->
           (fun ff ->
              Obj.magic
                (try_with
                   (fun uu___ ->
                      match () with
                      | () ->
                          FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (913)) (Prims.of_int (6))
                               (Prims.of_int (913)) (Prims.of_int (30)))
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (913)) (Prims.of_int (32))
                               (Prims.of_int (913)) (Prims.of_int (37)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (913)) (Prims.of_int (13))
                                     (Prims.of_int (913)) (Prims.of_int (30)))
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (913)) (Prims.of_int (6))
                                     (Prims.of_int (913)) (Prims.of_int (30)))
                                  (Obj.magic
                                     (FStar_Tactics_Visit.visit_tm ff t))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> ()))))
                            (fun uu___1 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> false)))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | Appears ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> true)))
                         | e ->
                             Obj.magic
                               (Obj.repr (FStar_Tactics_Effect.raise e)))
                        uu___))) uu___)
let rec (mk_abs :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
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
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (922)) (Prims.of_int (13))
                          (Prims.of_int (922)) (Prims.of_int (27)))
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (923)) (Prims.of_int (4))
                          (Prims.of_int (923)) (Prims.of_int (22)))
                       (Obj.magic (mk_abs args' t))
                       (fun uu___ ->
                          (fun t' ->
                             Obj.magic
                               (FStar_Tactics_Builtins.pack
                                  (FStar_Reflection_Data.Tv_Abs (a, t'))))
                            uu___)))) uu___1 uu___
let (string_to_term_with_lb :
  (Prims.string * FStar_Reflection_Types.term) Prims.list ->
    FStar_Reflection_Types.env ->
      Prims.string ->
        (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun letbindings ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (931))
             (Prims.of_int (20)) (Prims.of_int (934)) (Prims.of_int (27)))
          (Prims.mk_range "FStar.Tactics.Derived.fst" (Prims.of_int (931))
             (Prims.of_int (4)) (Prims.of_int (936)) (Prims.of_int (71)))
          (Obj.magic
             (FStar_Tactics_Util.fold_left
                (fun uu___ ->
                   fun uu___1 ->
                     match (uu___, uu___1) with
                     | ((e1, lb_bvs), (i, v)) ->
                         FStar_Tactics_Effect.tac_bind
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (932)) (Prims.of_int (20))
                              (Prims.of_int (932)) (Prims.of_int (37)))
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (932)) (Prims.of_int (8))
                              (Prims.of_int (933)) (Prims.of_int (25)))
                           (Obj.magic
                              (FStar_Tactics_Builtins.push_bv_dsenv e1 i))
                           (fun uu___2 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   match uu___2 with
                                   | (e2, bv) -> (e2, ((v, bv) :: lb_bvs)))))
                (e, []) letbindings))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (e1, lb_bvs) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (935)) (Prims.of_int (12))
                            (Prims.of_int (935)) (Prims.of_int (30)))
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (936)) (Prims.of_int (4))
                            (Prims.of_int (936)) (Prims.of_int (71)))
                         (Obj.magic
                            (FStar_Tactics_Builtins.string_to_term e1 t))
                         (fun uu___1 ->
                            (fun t1 ->
                               Obj.magic
                                 (FStar_Tactics_Util.fold_left
                                    (fun t2 ->
                                       fun uu___1 ->
                                         match uu___1 with
                                         | (i, bv) ->
                                             FStar_Tactics_Builtins.pack
                                               (FStar_Reflection_Data.Tv_Let
                                                  (false, [], bv, i, t2))) t1
                                    lb_bvs)) uu___1))) uu___)
let (trans : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Derived"; "lem_trans"])))