open Prims
let op_At :
  'uuuuu .
    unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list
  = fun uu___ -> FStar_List_Tot_Base.op_At
let (name_of_bv :
  FStar_Tactics_NamedView.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    FStar_Tactics_Unseal.unseal
      (FStar_Tactics_NamedView.inspect_bv bv).FStar_Reflection_V2_Data.ppname1
let (bv_to_string :
  FStar_Tactics_NamedView.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun bv -> name_of_bv bv
let (name_of_binder :
  FStar_Tactics_NamedView.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> FStar_Tactics_Unseal.unseal b.FStar_Tactics_NamedView.ppname
let (binder_to_string :
  FStar_Tactics_NamedView.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (46)) (Prims.of_int (2)) (Prims.of_int (46))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (46)) (Prims.of_int (2)) (Prims.of_int (46))
               (Prims.of_int (86))))) (Obj.magic (name_of_binder b))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (46)) (Prims.of_int (21))
                          (Prims.of_int (46)) (Prims.of_int (86)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                          (Prims.of_int (19)) (Prims.of_int (590))
                          (Prims.of_int (31)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (46)) (Prims.of_int (28))
                                (Prims.of_int (46)) (Prims.of_int (86)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.Derived.fst"
                                      (Prims.of_int (46)) (Prims.of_int (51))
                                      (Prims.of_int (46)) (Prims.of_int (86)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (590))
                                      (Prims.of_int (19))
                                      (Prims.of_int (590))
                                      (Prims.of_int (31)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (46))
                                            (Prims.of_int (59))
                                            (Prims.of_int (46))
                                            (Prims.of_int (86)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "prims.fst"
                                            (Prims.of_int (590))
                                            (Prims.of_int (19))
                                            (Prims.of_int (590))
                                            (Prims.of_int (31)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (46))
                                                  (Prims.of_int (59))
                                                  (Prims.of_int (46))
                                                  (Prims.of_int (80)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "prims.fst"
                                                  (Prims.of_int (590))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (590))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.term_to_string
                                               b.FStar_Tactics_NamedView.sort))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.strcat uu___1 ")"))))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Prims.strcat "::(" uu___1))))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Prims.strcat
                                       (Prims.string_of_int
                                          b.FStar_Tactics_NamedView.uniq)
                                       uu___1))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Prims.strcat "@@" uu___1))))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> Prims.strcat uu___ uu___1)))) uu___)
let (binding_to_string :
  FStar_Tactics_NamedView.binding ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> FStar_Tactics_Unseal.unseal b.FStar_Reflection_V2_Data.ppname3
let (type_of_var :
  FStar_Tactics_NamedView.namedv ->
    (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    FStar_Tactics_Unseal.unseal
      (FStar_Tactics_NamedView.inspect_namedv x).FStar_Reflection_V2_Data.sort
let (type_of_binding :
  FStar_Tactics_NamedView.binding -> FStar_Reflection_Types.typ) =
  fun x -> x.FStar_Reflection_V2_Data.sort3
exception Goal_not_trivial 
let (uu___is_Goal_not_trivial : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Goal_not_trivial -> true | uu___ -> false
let (goals :
  unit ->
    (FStar_Tactics_Types.goal Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (59)) (Prims.of_int (42)) (Prims.of_int (59))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (59)) (Prims.of_int (33)) (Prims.of_int (59))
               (Prims.of_int (50))))) (FStar_Tactics_Effect.get ())
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goals_of uu___1))
let (smt_goals :
  unit ->
    (FStar_Tactics_Types.goal Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (60)) (Prims.of_int (50)) (Prims.of_int (60))
               (Prims.of_int (58)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (60)) (Prims.of_int (37)) (Prims.of_int (60))
               (Prims.of_int (58))))) (FStar_Tactics_Effect.get ())
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.smt_goals_of uu___1))
let fail : 'a . Prims.string -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr =
  fun m -> FStar_Tactics_Effect.raise (FStar_Tactics_Common.TacticFailure m)
let fail_silently :
  'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (68)) (Prims.of_int (4)) (Prims.of_int (68))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (69)) (Prims.of_int (4)) (Prims.of_int (69))
               (Prims.of_int (30)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.set_urgency Prims.int_zero))
      (fun uu___ ->
         FStar_Tactics_Effect.raise (FStar_Tactics_Common.TacticFailure m))
let (_cur_goal :
  unit -> (FStar_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (73)) (Prims.of_int (10)) (Prims.of_int (73))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (73)) (Prims.of_int (4)) (Prims.of_int (75))
               (Prims.of_int (15))))) (Obj.magic (goals ()))
      (fun uu___1 ->
         match uu___1 with
         | [] -> fail "no more goals"
         | g::uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> g))
let (cur_env :
  unit -> (FStar_Reflection_Types.env, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (78)) (Prims.of_int (36)) (Prims.of_int (78))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (78)) (Prims.of_int (27)) (Prims.of_int (78))
               (Prims.of_int (50))))) (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goal_env uu___1))
let (cur_goal :
  unit -> (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (81)) (Prims.of_int (38)) (Prims.of_int (81))
               (Prims.of_int (52)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (81)) (Prims.of_int (28)) (Prims.of_int (81))
               (Prims.of_int (52))))) (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goal_type uu___1))
let (cur_witness :
  unit -> (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (84)) (Prims.of_int (45)) (Prims.of_int (84))
               (Prims.of_int (59)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (84)) (Prims.of_int (32)) (Prims.of_int (84))
               (Prims.of_int (59))))) (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.goal_witness uu___1))
let (cur_goal_safe :
  unit -> (FStar_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (91)) (Prims.of_int (9)) (Prims.of_int (91))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (91)) (Prims.of_int (3)) (Prims.of_int (92))
               (Prims.of_int (16)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (91)) (Prims.of_int (18))
                     (Prims.of_int (91)) (Prims.of_int (26)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (91)) (Prims.of_int (9))
                     (Prims.of_int (91)) (Prims.of_int (26)))))
            (FStar_Tactics_Effect.get ())
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 -> FStar_Tactics_Types.goals_of uu___1))))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> match uu___1 with | g::uu___3 -> g))
let (cur_vars :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (95)) (Prims.of_int (16)) (Prims.of_int (95))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (95)) (Prims.of_int (4)) (Prims.of_int (95))
               (Prims.of_int (28))))) (Obj.magic (cur_env ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Reflection_V2_Builtins.vars_of_env uu___1))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun pol ->
    fun f ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (99)) (Prims.of_int (18)) (Prims.of_int (99))
                 (Prims.of_int (37)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (100)) (Prims.of_int (4)) (Prims.of_int (103))
                 (Prims.of_int (5)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.get_guard_policy ()))
        (fun uu___ ->
           (fun old_pol ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (100)) (Prims.of_int (4))
                            (Prims.of_int (100)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (100)) (Prims.of_int (25))
                            (Prims.of_int (103)) (Prims.of_int (5)))))
                   (Obj.magic
                      (FStar_Tactics_V2_Builtins.set_guard_policy pol))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (101))
                                       (Prims.of_int (12))
                                       (Prims.of_int (101))
                                       (Prims.of_int (16)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (102))
                                       (Prims.of_int (4))
                                       (Prims.of_int (103))
                                       (Prims.of_int (5)))))
                              (Obj.magic (f ()))
                              (fun uu___1 ->
                                 (fun r ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (102))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (102))
                                                  (Prims.of_int (28)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (101))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (101))
                                                  (Prims.of_int (9)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.set_guard_policy
                                               old_pol))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 -> r)))) uu___1)))
                        uu___))) uu___)
let (exact :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu___ -> FStar_Tactics_V2_Builtins.t_exact true false t)
let (exact_with_ref :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu___ -> FStar_Tactics_V2_Builtins.t_exact true true t)
let (trivial : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (117)) (Prims.of_int (2)) (Prims.of_int (117))
               (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (117)) (Prims.of_int (62)) (Prims.of_int (121))
               (Prims.of_int (31)))))
      (Obj.magic
         (FStar_Tactics_V2_Builtins.norm
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
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (118)) (Prims.of_int (10))
                          (Prims.of_int (118)) (Prims.of_int (21)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (119)) (Prims.of_int (2))
                          (Prims.of_int (121)) (Prims.of_int (31)))))
                 (Obj.magic (cur_goal ()))
                 (fun uu___2 ->
                    (fun g ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (119)) (Prims.of_int (8))
                                     (Prims.of_int (119)) (Prims.of_int (25)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (119)) (Prims.of_int (2))
                                     (Prims.of_int (121)) (Prims.of_int (31)))))
                            (Obj.magic
                               (FStar_Reflection_V2_Formula.term_as_formula g))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | FStar_Reflection_V2_Formula.True_ ->
                                      Obj.magic
                                        (Obj.repr
                                           (exact
                                              (FStar_Reflection_V2_Builtins.pack_ln
                                                 (FStar_Reflection_V2_Data.Tv_Const
                                                    FStar_Reflection_V2_Data.C_Unit))))
                                  | uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.raise
                                              Goal_not_trivial))) uu___2)))
                      uu___2))) uu___1)
let (dismiss : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (133)) (Prims.of_int (10)) (Prims.of_int (133))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (133)) (Prims.of_int (4)) (Prims.of_int (135))
               (Prims.of_int (27))))) (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (Obj.repr (fail "dismiss: no more goals"))
            | uu___2::gs ->
                Obj.magic (Obj.repr (FStar_Tactics_V2_Builtins.set_goals gs)))
           uu___1)
let (flip : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (139)) (Prims.of_int (13)) (Prims.of_int (139))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (140)) (Prims.of_int (4)) (Prims.of_int (142))
               (Prims.of_int (42))))) (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun gs ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (140)) (Prims.of_int (10))
                          (Prims.of_int (140)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (140)) (Prims.of_int (4))
                          (Prims.of_int (142)) (Prims.of_int (42)))))
                 (Obj.magic (goals ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | [] ->
                           Obj.magic
                             (Obj.repr (fail "flip: less than two goals"))
                       | uu___2::[] ->
                           Obj.magic
                             (Obj.repr (fail "flip: less than two goals"))
                       | g1::g2::gs1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_V2_Builtins.set_goals (g2 ::
                                   g1 :: gs1)))) uu___1))) uu___1)
let (qed : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (146)) (Prims.of_int (10)) (Prims.of_int (146))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (146)) (Prims.of_int (4)) (Prims.of_int (148))
               (Prims.of_int (32))))) (Obj.magic (goals ()))
      (fun uu___1 ->
         match uu___1 with
         | [] -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())
         | uu___2 -> fail "qed: not done!")
let (debug : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (154)) (Prims.of_int (7)) (Prims.of_int (154))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (154)) (Prims.of_int (4)) (Prims.of_int (154))
               (Prims.of_int (32)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.debugging ()))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then Obj.magic (Obj.repr (FStar_Tactics_V2_Builtins.print m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let (smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (161)) (Prims.of_int (10)) (Prims.of_int (161))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (161)) (Prims.of_int (4)) (Prims.of_int (167))
               (Prims.of_int (11)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (161)) (Prims.of_int (10))
                     (Prims.of_int (161)) (Prims.of_int (18)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (161)) (Prims.of_int (10))
                     (Prims.of_int (161)) (Prims.of_int (32)))))
            (Obj.magic (goals ()))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (161)) (Prims.of_int (20))
                                (Prims.of_int (161)) (Prims.of_int (32)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (161)) (Prims.of_int (10))
                                (Prims.of_int (161)) (Prims.of_int (32)))))
                       (Obj.magic (smt_goals ()))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> (uu___1, uu___2))))) uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | ([], uu___2) ->
                Obj.magic (Obj.repr (fail "smt: no active goals"))
            | (g::gs, gs') ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (165)) (Prims.of_int (8))
                                 (Prims.of_int (165)) (Prims.of_int (20)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (166)) (Prims.of_int (8))
                                 (Prims.of_int (166)) (Prims.of_int (32)))))
                        (Obj.magic (FStar_Tactics_V2_Builtins.set_goals gs))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              Obj.magic
                                (FStar_Tactics_V2_Builtins.set_smt_goals (g
                                   :: gs'))) uu___2)))) uu___1)
let (idtac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
      uu___
let (later : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (173)) (Prims.of_int (10)) (Prims.of_int (173))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (173)) (Prims.of_int (4)) (Prims.of_int (175))
               (Prims.of_int (33))))) (Obj.magic (goals ()))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | g::gs ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_V2_Builtins.set_goals ((op_At ()) gs [g])))
            | uu___2 -> Obj.magic (Obj.repr (fail "later: no goals"))) uu___1)
let (apply :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Builtins.t_apply true false false t
let (apply_noinst :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Builtins.t_apply true true false t
let (apply_lemma :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Builtins.t_apply_lemma false false t
let (trefl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_V2_Builtins.t_trefl false
let (trefl_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_V2_Builtins.t_trefl true
let (commute_applied_match :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_V2_Builtins.t_commute_applied_match ()
let (apply_lemma_noinst :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Builtins.t_apply_lemma true false t
let (apply_lemma_rw :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Builtins.t_apply_lemma false true t
let (apply_raw :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Builtins.t_apply false false false t
let (exact_guard :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStar_Tactics_Types.Goal
      (fun uu___ -> FStar_Tactics_V2_Builtins.t_exact true false t)
let (t_pointwise :
  FStar_Tactics_Types.direction ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun tau ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (234)) (Prims.of_int (4)) (Prims.of_int (234))
                 (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (235)) (Prims.of_int (4)) (Prims.of_int (239))
                 (Prims.of_int (24)))))
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
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (237)) (Prims.of_int (4))
                            (Prims.of_int (237)) (Prims.of_int (10)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (239)) (Prims.of_int (2))
                            (Prims.of_int (239)) (Prims.of_int (24)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> fun uu___1 -> tau ()))
                   (fun uu___ ->
                      (fun rw ->
                         Obj.magic
                           (FStar_Tactics_V2_Builtins.ctrl_rewrite d ctrl rw))
                        uu___))) uu___)
let (topdown_rewrite :
  (FStar_Tactics_NamedView.term ->
     ((Prims.bool * Prims.int), unit) FStar_Tactics_Effect.tac_repr)
    ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ctrl ->
    fun rw ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (263)) (Prims.of_int (49))
                 (Prims.of_int (272)) (Prims.of_int (10)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (274)) (Prims.of_int (4)) (Prims.of_int (274))
                 (Prims.of_int (33)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (264)) (Prims.of_int (17))
                           (Prims.of_int (264)) (Prims.of_int (23)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (263)) (Prims.of_int (49))
                           (Prims.of_int (272)) (Prims.of_int (10)))))
                  (Obj.magic (ctrl t))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | (b, i) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Derived.fst"
                                          (Prims.of_int (266))
                                          (Prims.of_int (8))
                                          (Prims.of_int (270))
                                          (Prims.of_int (58)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Derived.fst"
                                          (Prims.of_int (272))
                                          (Prims.of_int (6))
                                          (Prims.of_int (272))
                                          (Prims.of_int (10)))))
                                 (match i with
                                  | uu___2 when uu___2 = Prims.int_zero ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           FStar_Tactics_Types.Continue)
                                  | uu___2 when uu___2 = Prims.int_one ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           FStar_Tactics_Types.Skip)
                                  | uu___2 when uu___2 = (Prims.of_int (2))
                                      ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           FStar_Tactics_Types.Abort)
                                  | uu___2 ->
                                      fail
                                        "topdown_rewrite: bad value from ctrl")
                                 (fun f ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> (b, f))))) uu___1)))
        (fun uu___ ->
           (fun ctrl' ->
              Obj.magic
                (FStar_Tactics_V2_Builtins.ctrl_rewrite
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (280)) (Prims.of_int (13)) (Prims.of_int (280))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (280)) (Prims.of_int (4)) (Prims.of_int (280))
               (Prims.of_int (25)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Reflection_V2_Builtins.moduleof uu___1))
let (open_modules :
  unit ->
    (FStar_Reflection_Types.name Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (283)) (Prims.of_int (21)) (Prims.of_int (283))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (283)) (Prims.of_int (4)) (Prims.of_int (283))
               (Prims.of_int (33)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              FStar_Reflection_V2_Builtins.env_open_modules uu___1))
let (fresh_uvar :
  FStar_Reflection_Types.typ FStar_Pervasives_Native.option ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (286)) (Prims.of_int (12)) (Prims.of_int (286))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (287)) (Prims.of_int (4)) (Prims.of_int (287))
               (Prims.of_int (16))))) (Obj.magic (cur_env ()))
      (fun uu___ ->
         (fun e -> Obj.magic (FStar_Tactics_V2_Builtins.uvar_env e o)) uu___)
let (unify :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (290)) (Prims.of_int (12))
                 (Prims.of_int (290)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (291)) (Prims.of_int (4)) (Prims.of_int (291))
                 (Prims.of_int (21))))) (Obj.magic (cur_env ()))
        (fun uu___ ->
           (fun e -> Obj.magic (FStar_Tactics_V2_Builtins.unify_env e t1 t2))
             uu___)
let (unify_guard :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (294)) (Prims.of_int (12))
                 (Prims.of_int (294)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (295)) (Prims.of_int (4)) (Prims.of_int (295))
                 (Prims.of_int (27))))) (Obj.magic (cur_env ()))
        (fun uu___ ->
           (fun e ->
              Obj.magic (FStar_Tactics_V2_Builtins.unify_guard_env e t1 t2))
             uu___)
let (tmatch :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (298)) (Prims.of_int (12))
                 (Prims.of_int (298)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (299)) (Prims.of_int (4)) (Prims.of_int (299))
                 (Prims.of_int (21))))) (Obj.magic (cur_env ()))
        (fun uu___ ->
           (fun e -> Obj.magic (FStar_Tactics_V2_Builtins.match_env e t1 t2))
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
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (305)) (Prims.of_int (4))
                   (Prims.of_int (306)) (Prims.of_int (31)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (306)) (Prims.of_int (32))
                   (Prims.of_int (319)) (Prims.of_int (10)))))
          (if n < Prims.int_zero
           then fail "divide: negative n"
           else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (307)) (Prims.of_int (18))
                              (Prims.of_int (307)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (306)) (Prims.of_int (32))
                              (Prims.of_int (319)) (Prims.of_int (10)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (307)) (Prims.of_int (18))
                                    (Prims.of_int (307)) (Prims.of_int (26)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (307)) (Prims.of_int (18))
                                    (Prims.of_int (307)) (Prims.of_int (40)))))
                           (Obj.magic (goals ()))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (307))
                                               (Prims.of_int (28))
                                               (Prims.of_int (307))
                                               (Prims.of_int (40)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (307))
                                               (Prims.of_int (18))
                                               (Prims.of_int (307))
                                               (Prims.of_int (40)))))
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
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (308))
                                             (Prims.of_int (19))
                                             (Prims.of_int (308))
                                             (Prims.of_int (45)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (307))
                                             (Prims.of_int (43))
                                             (Prims.of_int (319))
                                             (Prims.of_int (10)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          FStar_List_Tot_Base.splitAt n gs))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match uu___2 with
                                          | (gs1, gs2) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.V2.Derived.fst"
                                                            (Prims.of_int (310))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (310))
                                                            (Prims.of_int (17)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.V2.Derived.fst"
                                                            (Prims.of_int (310))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (319))
                                                            (Prims.of_int (10)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_V2_Builtins.set_goals
                                                         gs1))
                                                   (fun uu___3 ->
                                                      (fun uu___3 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_V2_Builtins.set_smt_goals
                                                                    []))
                                                              (fun uu___4 ->
                                                                 (fun uu___4
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (l ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (goals ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (42)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_goals
                                                                    gs2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_smt_goals
                                                                    []))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (r ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun y ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (goals ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (42)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_goals
                                                                    ((op_At
                                                                    ()) gsl
                                                                    gsr)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_smt_goals
                                                                    ((op_At
                                                                    ()) sgs
                                                                    ((op_At
                                                                    ()) sgsl
                                                                    sgsr))))
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
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (323)) (Prims.of_int (23))
                            (Prims.of_int (323)) (Prims.of_int (53)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (323)) (Prims.of_int (57))
                            (Prims.of_int (323)) (Prims.of_int (59)))))
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (329)) (Prims.of_int (10)) (Prims.of_int (329))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (329)) (Prims.of_int (4)) (Prims.of_int (336))
               (Prims.of_int (9))))) (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] -> Obj.magic (Obj.repr (fail "focus: no goals"))
            | g::gs ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (332)) (Prims.of_int (18))
                                 (Prims.of_int (332)) (Prims.of_int (30)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (333)) (Prims.of_int (8))
                                 (Prims.of_int (336)) (Prims.of_int (9)))))
                        (Obj.magic (smt_goals ()))
                        (fun uu___1 ->
                           (fun sgs ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (333))
                                            (Prims.of_int (8))
                                            (Prims.of_int (333))
                                            (Prims.of_int (21)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (333))
                                            (Prims.of_int (23))
                                            (Prims.of_int (336))
                                            (Prims.of_int (9)))))
                                   (Obj.magic
                                      (FStar_Tactics_V2_Builtins.set_goals
                                         [g]))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (333))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (333))
                                                       (Prims.of_int (39)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (333))
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (336))
                                                       (Prims.of_int (9)))))
                                              (Obj.magic
                                                 (FStar_Tactics_V2_Builtins.set_smt_goals
                                                    []))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Derived.fst"
                                                                  (Prims.of_int (334))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (334))
                                                                  (Prims.of_int (20)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Derived.fst"
                                                                  (Prims.of_int (335))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (336))
                                                                  (Prims.of_int (9)))))
                                                         (Obj.magic (t ()))
                                                         (fun uu___3 ->
                                                            (fun x ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (9)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (goals ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (op_At ())
                                                                    uu___3 gs))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_goals
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (smt_goals
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (op_At ())
                                                                    uu___4
                                                                    sgs))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_smt_goals
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    x))))
                                                                    uu___3)))
                                                              uu___3)))
                                                   uu___2))) uu___1))) uu___1))))
           uu___)
let (dump1 : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m -> focus (fun uu___ -> FStar_Tactics_V2_Builtins.dump m)
let rec mapAll :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (342)) (Prims.of_int (10)) (Prims.of_int (342))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (342)) (Prims.of_int (4)) (Prims.of_int (344))
               (Prims.of_int (66))))) (Obj.magic (goals ()))
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
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (344)) (Prims.of_int (27))
                                 (Prims.of_int (344)) (Prims.of_int (58)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (344)) (Prims.of_int (13))
                                 (Prims.of_int (344)) (Prims.of_int (66)))))
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (348)) (Prims.of_int (10)) (Prims.of_int (348))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (348)) (Prims.of_int (4)) (Prims.of_int (350))
               (Prims.of_int (60))))) (Obj.magic (goals ()))
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
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (350)) (Prims.of_int (22))
                                 (Prims.of_int (350)) (Prims.of_int (54)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (350)) (Prims.of_int (58))
                                 (Prims.of_int (350)) (Prims.of_int (60)))))
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (353)) (Prims.of_int (18)) (Prims.of_int (353))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (352)) (Prims.of_int (50)) (Prims.of_int (359))
               (Prims.of_int (28)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (353)) (Prims.of_int (18))
                     (Prims.of_int (353)) (Prims.of_int (26)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (353)) (Prims.of_int (18))
                     (Prims.of_int (353)) (Prims.of_int (40)))))
            (Obj.magic (goals ()))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (353)) (Prims.of_int (28))
                                (Prims.of_int (353)) (Prims.of_int (40)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (353)) (Prims.of_int (18))
                                (Prims.of_int (353)) (Prims.of_int (40)))))
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
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (354)) (Prims.of_int (4))
                              (Prims.of_int (354)) (Prims.of_int (17)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (355)) (Prims.of_int (4))
                              (Prims.of_int (359)) (Prims.of_int (28)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.set_goals sgs))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (355))
                                         (Prims.of_int (4))
                                         (Prims.of_int (355))
                                         (Prims.of_int (20)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (356))
                                         (Prims.of_int (4))
                                         (Prims.of_int (359))
                                         (Prims.of_int (28)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.set_smt_goals
                                      []))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (356))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (356))
                                                    (Prims.of_int (13)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (356))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (359))
                                                    (Prims.of_int (28)))))
                                           (Obj.magic (iterAll t))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (357))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (357))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (356))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (359))
                                                               (Prims.of_int (28)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (28)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (42)))))
                                                            (Obj.magic
                                                               (goals ()))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (42)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_goals
                                                                    gs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_smt_goals
                                                                    ((op_At
                                                                    ()) gs'
                                                                    sgs')))
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
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (365)) (Prims.of_int (21))
                      (Prims.of_int (365)) (Prims.of_int (25)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (365)) (Prims.of_int (27))
                      (Prims.of_int (365)) (Prims.of_int (36)))))
             (Obj.magic (f ()))
             (fun uu___1 -> (fun uu___1 -> Obj.magic (iterAll g)) uu___1))
let (exact_args :
  FStar_Reflection_V2_Data.aqualv Prims.list ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun qs ->
    fun t ->
      focus
        (fun uu___ ->
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (369)) (Prims.of_int (16))
                      (Prims.of_int (369)) (Prims.of_int (39)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (369)) (Prims.of_int (42))
                      (Prims.of_int (375)) (Prims.of_int (44)))))
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___1 -> FStar_List_Tot_Base.length qs))
             (fun uu___1 ->
                (fun n ->
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (370)) (Prims.of_int (18))
                                 (Prims.of_int (370)) (Prims.of_int (55)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (370)) (Prims.of_int (58))
                                 (Prims.of_int (375)) (Prims.of_int (44)))))
                        (Obj.magic
                           (FStar_Tactics_Util.repeatn n
                              (fun uu___1 ->
                                 fresh_uvar FStar_Pervasives_Native.None)))
                        (fun uu___1 ->
                           (fun uvs ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (371))
                                            (Prims.of_int (17))
                                            (Prims.of_int (371))
                                            (Prims.of_int (38)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (372))
                                            (Prims.of_int (8))
                                            (Prims.of_int (375))
                                            (Prims.of_int (44)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (371))
                                                  (Prims.of_int (26))
                                                  (Prims.of_int (371))
                                                  (Prims.of_int (38)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (371))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (371))
                                                  (Prims.of_int (38)))))
                                         (Obj.magic
                                            (FStar_Tactics_Util.zip uvs qs))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 FStar_Reflection_V2_Derived.mk_app
                                                   t uu___1))))
                                   (fun uu___1 ->
                                      (fun t' ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (372))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (372))
                                                       (Prims.of_int (16)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (373))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (375))
                                                       (Prims.of_int (44)))))
                                              (Obj.magic (exact t'))
                                              (fun uu___1 ->
                                                 (fun uu___1 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Util.iter
                                                         (fun uu___2 ->
                                                            (fun uv ->
                                                               if
                                                                 FStar_Reflection_V2_Derived.is_uvar
                                                                   uv
                                                               then
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.unshelve
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
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun n ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (379)) (Prims.of_int (15))
                 (Prims.of_int (379)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (379)) (Prims.of_int (4)) (Prims.of_int (379))
                 (Prims.of_int (51)))))
        (Obj.magic
           (FStar_Tactics_Util.repeatn n
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 -> FStar_Reflection_V2_Data.Q_Explicit)))
                   uu___)))
        (fun uu___ -> (fun uu___ -> Obj.magic (exact_args uu___ t)) uu___)
let (ngoals : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (382)) (Prims.of_int (47)) (Prims.of_int (382))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (382)) (Prims.of_int (26)) (Prims.of_int (382))
               (Prims.of_int (57))))) (Obj.magic (goals ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_List_Tot_Base.length uu___1))
let (ngoals_smt : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (385)) (Prims.of_int (51)) (Prims.of_int (385))
               (Prims.of_int (65)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (385)) (Prims.of_int (30)) (Prims.of_int (385))
               (Prims.of_int (65))))) (Obj.magic (smt_goals ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_List_Tot_Base.length uu___1))
let (fresh_namedv_named :
  Prims.string ->
    (FStar_Tactics_NamedView.namedv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (389)) (Prims.of_int (10)) (Prims.of_int (389))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (390)) (Prims.of_int (2)) (Prims.of_int (394))
               (Prims.of_int (4)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.fresh ()))
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              FStar_Tactics_NamedView.pack_namedv
                {
                  FStar_Reflection_V2_Data.uniq = n;
                  FStar_Reflection_V2_Data.sort =
                    (FStar_Sealed.seal
                       (FStar_Reflection_V2_Builtins.pack_ln
                          FStar_Reflection_V2_Data.Tv_Unknown));
                  FStar_Reflection_V2_Data.ppname = (FStar_Sealed.seal s)
                }))
let (fresh_namedv :
  unit ->
    (FStar_Tactics_NamedView.namedv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (399)) (Prims.of_int (10)) (Prims.of_int (399))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (400)) (Prims.of_int (2)) (Prims.of_int (404))
               (Prims.of_int (4)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.fresh ()))
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              FStar_Tactics_NamedView.pack_namedv
                {
                  FStar_Reflection_V2_Data.uniq = n;
                  FStar_Reflection_V2_Data.sort =
                    (FStar_Sealed.seal
                       (FStar_Reflection_V2_Builtins.pack_ln
                          FStar_Reflection_V2_Data.Tv_Unknown));
                  FStar_Reflection_V2_Data.ppname =
                    (FStar_Sealed.seal
                       (Prims.strcat "x" (Prims.string_of_int n)))
                }))
let (fresh_binder_named :
  Prims.string ->
    FStar_Reflection_Types.typ ->
      (FStar_Tactics_NamedView.simple_binder, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (407)) (Prims.of_int (10))
                 (Prims.of_int (407)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (409)) (Prims.of_int (4)) (Prims.of_int (413))
                 (Prims.of_int (17)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.fresh ()))
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                {
                  FStar_Tactics_NamedView.uniq = n;
                  FStar_Tactics_NamedView.ppname = (FStar_Sealed.seal s);
                  FStar_Tactics_NamedView.sort = t;
                  FStar_Tactics_NamedView.qual =
                    FStar_Reflection_V2_Data.Q_Explicit;
                  FStar_Tactics_NamedView.attrs = []
                }))
let (fresh_binder :
  FStar_Reflection_Types.typ ->
    (FStar_Tactics_NamedView.simple_binder, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (417)) (Prims.of_int (10)) (Prims.of_int (417))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (419)) (Prims.of_int (4)) (Prims.of_int (423))
               (Prims.of_int (17)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.fresh ()))
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              {
                FStar_Tactics_NamedView.uniq = n;
                FStar_Tactics_NamedView.ppname =
                  (FStar_Sealed.seal
                     (Prims.strcat "x" (Prims.string_of_int n)));
                FStar_Tactics_NamedView.sort = t;
                FStar_Tactics_NamedView.qual =
                  FStar_Reflection_V2_Data.Q_Explicit;
                FStar_Tactics_NamedView.attrs = []
              }))
let (fresh_implicit_binder :
  FStar_Reflection_Types.typ ->
    (FStar_Tactics_NamedView.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (427)) (Prims.of_int (10)) (Prims.of_int (427))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (429)) (Prims.of_int (4)) (Prims.of_int (433))
               (Prims.of_int (17)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.fresh ()))
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              {
                FStar_Tactics_NamedView.uniq = n;
                FStar_Tactics_NamedView.ppname =
                  (FStar_Sealed.seal
                     (Prims.strcat "x" (Prims.string_of_int n)));
                FStar_Tactics_NamedView.sort = t;
                FStar_Tactics_NamedView.qual =
                  FStar_Reflection_V2_Data.Q_Implicit;
                FStar_Tactics_NamedView.attrs = []
              }))
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
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (447)) (Prims.of_int (10))
                 (Prims.of_int (447)) (Prims.of_int (17)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (447)) (Prims.of_int (4)) (Prims.of_int (449))
                 (Prims.of_int (16)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.catch f))
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
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (452)) (Prims.of_int (13))
                        (Prims.of_int (452)) (Prims.of_int (19)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (452)) (Prims.of_int (8))
                        (Prims.of_int (452)) (Prims.of_int (19)))))
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
      (fun uu___ -> (fun uu___ -> Obj.magic (fail "no tactics to try")) uu___)
      ()
let rec repeat :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (469)) (Prims.of_int (10)) (Prims.of_int (469))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (469)) (Prims.of_int (4)) (Prims.of_int (471))
               (Prims.of_int (28)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.catch t))
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
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (471)) (Prims.of_int (20))
                                 (Prims.of_int (471)) (Prims.of_int (28)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (471)) (Prims.of_int (15))
                                 (Prims.of_int (471)) (Prims.of_int (28)))))
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (474)) (Prims.of_int (4)) (Prims.of_int (474))
               (Prims.of_int (8)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (474)) (Prims.of_int (4)) (Prims.of_int (474))
               (Prims.of_int (20))))) (Obj.magic (t ()))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (474)) (Prims.of_int (12))
                          (Prims.of_int (474)) (Prims.of_int (20)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (474)) (Prims.of_int (4))
                          (Prims.of_int (474)) (Prims.of_int (20)))))
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (477)) (Prims.of_int (12)) (Prims.of_int (477))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (477)) (Prims.of_int (24)) (Prims.of_int (477))
               (Prims.of_int (26))))) (Obj.magic (repeat f))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (norm_term :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (481)) (Prims.of_int (8)) (Prims.of_int (482))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (484)) (Prims.of_int (4)) (Prims.of_int (484))
                 (Prims.of_int (23)))))
        (Obj.magic
           (try_with (fun uu___ -> match () with | () -> cur_env ())
              (fun uu___ -> FStar_Tactics_V2_Builtins.top_env ())))
        (fun uu___ ->
           (fun e ->
              Obj.magic (FStar_Tactics_V2_Builtins.norm_term_env e s t))
             uu___)
let (join_all_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (491)) (Prims.of_int (16)) (Prims.of_int (491))
               (Prims.of_int (38)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (490)) (Prims.of_int (27)) (Prims.of_int (497))
               (Prims.of_int (20)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (491)) (Prims.of_int (16))
                     (Prims.of_int (491)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (491)) (Prims.of_int (16))
                     (Prims.of_int (491)) (Prims.of_int (38)))))
            (Obj.magic (goals ()))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (491)) (Prims.of_int (26))
                                (Prims.of_int (491)) (Prims.of_int (38)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (491)) (Prims.of_int (16))
                                (Prims.of_int (491)) (Prims.of_int (38)))))
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
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (492)) (Prims.of_int (2))
                              (Prims.of_int (492)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (493)) (Prims.of_int (2))
                              (Prims.of_int (497)) (Prims.of_int (20)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.set_smt_goals []))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (493))
                                         (Prims.of_int (2))
                                         (Prims.of_int (493))
                                         (Prims.of_int (15)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (494))
                                         (Prims.of_int (2))
                                         (Prims.of_int (497))
                                         (Prims.of_int (20)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.set_goals sgs))
                                (fun uu___3 ->
                                   (fun uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (494))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (494))
                                                    (Prims.of_int (14)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (494))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (497))
                                                    (Prims.of_int (20)))))
                                           (Obj.magic
                                              (repeat'
                                                 FStar_Tactics_V2_Builtins.join))
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (495))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (495))
                                                               (Prims.of_int (21)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (496))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (497))
                                                               (Prims.of_int (20)))))
                                                      (Obj.magic (goals ()))
                                                      (fun uu___5 ->
                                                         (fun sgs' ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (14)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (20)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Builtins.set_goals
                                                                    gs))
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_smt_goals
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
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (500)) (Prims.of_int (22))
                 (Prims.of_int (500)) (Prims.of_int (28)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (500)) (Prims.of_int (32))
                 (Prims.of_int (500)) (Prims.of_int (34)))))
        (Obj.magic (tau ()))
        (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let rec repeatseq :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (504)) (Prims.of_int (12)) (Prims.of_int (504))
               (Prims.of_int (82)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (504)) (Prims.of_int (86)) (Prims.of_int (504))
               (Prims.of_int (88)))))
      (Obj.magic
         (trytac
            (fun uu___ ->
               seq (discard t) (discard (fun uu___1 -> repeatseq t)))))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (tadmit : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Builtins.tadmit_t
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_Unit))
let (admit1 : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> tadmit ()
let (admit_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (512)) (Prims.of_int (12)) (Prims.of_int (512))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (513)) (Prims.of_int (4)) (Prims.of_int (513))
               (Prims.of_int (6))))) (Obj.magic (repeat tadmit))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (is_guard : unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (517)) (Prims.of_int (27)) (Prims.of_int (517))
               (Prims.of_int (41)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (517)) (Prims.of_int (4)) (Prims.of_int (517))
               (Prims.of_int (41))))) (Obj.magic (_cur_goal ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_Types.is_guard uu___1))
let (skip_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (520)) (Prims.of_int (7)) (Prims.of_int (520))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (520)) (Prims.of_int (4)) (Prims.of_int (522))
               (Prims.of_int (16))))) (Obj.magic (is_guard ()))
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (smt ()))
            else Obj.magic (Obj.repr (fail ""))) uu___1)
let (guards_to_smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (525)) (Prims.of_int (12)) (Prims.of_int (525))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (526)) (Prims.of_int (4)) (Prims.of_int (526))
               (Prims.of_int (6))))) (Obj.magic (repeat skip_guard))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (simpl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Builtins.norm
      [FStar_Pervasives.simplify; FStar_Pervasives.primops]
let (whnf : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Builtins.norm
      [FStar_Pervasives.weak;
      FStar_Pervasives.hnf;
      FStar_Pervasives.primops;
      FStar_Pervasives.delta]
let (compute : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Builtins.norm
      [FStar_Pervasives.primops;
      FStar_Pervasives.iota;
      FStar_Pervasives.delta;
      FStar_Pervasives.zeta]
let (intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> repeat FStar_Tactics_V2_Builtins.intro
let (intros' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (534)) (Prims.of_int (36)) (Prims.of_int (534))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (534)) (Prims.of_int (49)) (Prims.of_int (534))
               (Prims.of_int (51))))) (Obj.magic (intros ()))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (destruct :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (535)) (Prims.of_int (37)) (Prims.of_int (535))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (535)) (Prims.of_int (54)) (Prims.of_int (535))
               (Prims.of_int (56)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.t_destruct tm))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (destruct_intros :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    seq
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (536)) (Prims.of_int (59))
                    (Prims.of_int (536)) (Prims.of_int (72)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (536)) (Prims.of_int (76))
                    (Prims.of_int (536)) (Prims.of_int (78)))))
           (Obj.magic (FStar_Tactics_V2_Builtins.t_destruct tm))
           (fun uu___1 ->
              FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) intros'
let __cut : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
let (tcut :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (542)) (Prims.of_int (12)) (Prims.of_int (542))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (542)) (Prims.of_int (26)) (Prims.of_int (545))
               (Prims.of_int (12))))) (Obj.magic (cur_goal ()))
      (fun uu___ ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (543)) (Prims.of_int (13))
                          (Prims.of_int (543)) (Prims.of_int (37)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (544)) (Prims.of_int (4))
                          (Prims.of_int (545)) (Prims.of_int (12)))))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_Reflection_V2_Derived.mk_e_app
                         (FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_FVar
                               (FStar_Reflection_V2_Builtins.pack_fv
                                  ["FStar";
                                  "Tactics";
                                  "V2";
                                  "Derived";
                                  "__cut"]))) [t; g]))
                 (fun uu___ ->
                    (fun tt ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (544)) (Prims.of_int (4))
                                     (Prims.of_int (544)) (Prims.of_int (12)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (545)) (Prims.of_int (4))
                                     (Prims.of_int (545)) (Prims.of_int (12)))))
                            (Obj.magic (apply tt))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_V2_Builtins.intro ()))
                                 uu___))) uu___))) uu___)
let (pose :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (548)) (Prims.of_int (4)) (Prims.of_int (548))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (549)) (Prims.of_int (4)) (Prims.of_int (551))
               (Prims.of_int (12)))))
      (Obj.magic
         (apply
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V2"; "Derived"; "__cut"])))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (549)) (Prims.of_int (4))
                          (Prims.of_int (549)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (550)) (Prims.of_int (4))
                          (Prims.of_int (551)) (Prims.of_int (12)))))
                 (Obj.magic (flip ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (550)) (Prims.of_int (4))
                                     (Prims.of_int (550)) (Prims.of_int (11)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (551)) (Prims.of_int (4))
                                     (Prims.of_int (551)) (Prims.of_int (12)))))
                            (Obj.magic (exact t))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  Obj.magic
                                    (FStar_Tactics_V2_Builtins.intro ()))
                                 uu___2))) uu___1))) uu___)
let (intro_as :
  Prims.string ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (554)) (Prims.of_int (12)) (Prims.of_int (554))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (555)) (Prims.of_int (4)) (Prims.of_int (555))
               (Prims.of_int (17)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
      (fun uu___ ->
         (fun b -> Obj.magic (FStar_Tactics_V2_Builtins.rename_to b s)) uu___)
let (pose_as :
  Prims.string ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (558)) (Prims.of_int (12))
                 (Prims.of_int (558)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (559)) (Prims.of_int (4)) (Prims.of_int (559))
                 (Prims.of_int (17))))) (Obj.magic (pose t))
        (fun uu___ ->
           (fun b -> Obj.magic (FStar_Tactics_V2_Builtins.rename_to b s))
             uu___)
let for_each_binding :
  'a .
    (FStar_Tactics_NamedView.binding ->
       ('a, unit) FStar_Tactics_Effect.tac_repr)
      -> ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (562)) (Prims.of_int (10)) (Prims.of_int (562))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (562)) (Prims.of_int (4)) (Prims.of_int (562))
               (Prims.of_int (23))))) (Obj.magic (cur_vars ()))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Util.map f uu___)) uu___)
let rec (revert_all :
  FStar_Tactics_NamedView.binding Prims.list ->
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
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (567)) (Prims.of_int (15))
                            (Prims.of_int (567)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (568)) (Prims.of_int (13))
                            (Prims.of_int (568)) (Prims.of_int (26)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.revert ()))
                   (fun uu___1 ->
                      (fun uu___1 -> Obj.magic (revert_all tl)) uu___1))))
      uu___
let (binder_sort :
  FStar_Tactics_NamedView.binder -> FStar_Reflection_Types.typ) =
  fun b -> b.FStar_Tactics_NamedView.sort
let rec (__assumption_aux :
  FStar_Tactics_NamedView.binding Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun xs ->
       match xs with
       | [] -> Obj.magic (Obj.repr (fail "no assumption matches goal"))
       | b::bs ->
           Obj.magic
             (Obj.repr
                (try_with
                   (fun uu___ ->
                      match () with
                      | () ->
                          exact
                            (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                               b))
                   (fun uu___ ->
                      try_with
                        (fun uu___1 ->
                           match () with
                           | () ->
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Derived.fst"
                                          (Prims.of_int (580))
                                          (Prims.of_int (13))
                                          (Prims.of_int (580))
                                          (Prims.of_int (48)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Derived.fst"
                                          (Prims.of_int (581))
                                          (Prims.of_int (13))
                                          (Prims.of_int (581))
                                          (Prims.of_int (20)))))
                                 (Obj.magic
                                    (apply
                                       (FStar_Reflection_V2_Builtins.pack_ln
                                          (FStar_Reflection_V2_Data.Tv_FVar
                                             (FStar_Reflection_V2_Builtins.pack_fv
                                                ["FStar";
                                                "Squash";
                                                "return_squash"])))))
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       Obj.magic
                                         (exact
                                            (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                               b))) uu___2))
                        (fun uu___1 -> __assumption_aux bs))))) uu___
let (assumption : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (585)) (Prims.of_int (21)) (Prims.of_int (585))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (585)) (Prims.of_int (4)) (Prims.of_int (585))
               (Prims.of_int (34))))) (Obj.magic (cur_vars ()))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (__assumption_aux uu___1)) uu___1)
let (destruct_equality_implication :
  FStar_Tactics_NamedView.term ->
    ((FStar_Reflection_V2_Formula.formula * FStar_Tactics_NamedView.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (588)) (Prims.of_int (10)) (Prims.of_int (588))
               (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (588)) (Prims.of_int (4)) (Prims.of_int (595))
               (Prims.of_int (15)))))
      (Obj.magic (FStar_Reflection_V2_Formula.term_as_formula t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_V2_Formula.Implies (lhs, rhs) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (590)) (Prims.of_int (18))
                                 (Prims.of_int (590)) (Prims.of_int (38)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (591)) (Prims.of_int (14))
                                 (Prims.of_int (593)) (Prims.of_int (19)))))
                        (Obj.magic
                           (FStar_Reflection_V2_Formula.term_as_formula' lhs))
                        (fun lhs1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                match lhs1 with
                                | FStar_Reflection_V2_Formula.Comp
                                    (FStar_Reflection_V2_Formula.Eq uu___2,
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
  FStar_Tactics_NamedView.binding ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    op_Less_Bar_Greater
      (op_Less_Bar_Greater (fun uu___ -> FStar_Tactics_V2_Builtins.rewrite x)
         (fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                       (Prims.of_int (604)) (Prims.of_int (20))
                       (Prims.of_int (604)) (Prims.of_int (32)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                       (Prims.of_int (605)) (Prims.of_int (20))
                       (Prims.of_int (606)) (Prims.of_int (29)))))
              (Obj.magic (FStar_Tactics_V2_Builtins.var_retype x))
              (fun uu___1 ->
                 (fun uu___1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (605)) (Prims.of_int (20))
                                  (Prims.of_int (605)) (Prims.of_int (43)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (606)) (Prims.of_int (20))
                                  (Prims.of_int (606)) (Prims.of_int (29)))))
                         (Obj.magic
                            (apply_lemma
                               (FStar_Reflection_V2_Builtins.pack_ln
                                  (FStar_Reflection_V2_Data.Tv_FVar
                                     (FStar_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "V2";
                                        "Derived";
                                        "__eq_sym"])))))
                         (fun uu___2 ->
                            (fun uu___2 ->
                               Obj.magic
                                 (FStar_Tactics_V2_Builtins.rewrite x))
                              uu___2))) uu___1)))
      (fun uu___ -> (fun uu___ -> Obj.magic (fail "rewrite' failed")) uu___)
      ()
let rec (try_rewrite_equality :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.binding Prims.list ->
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
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (614)) (Prims.of_int (20))
                                (Prims.of_int (614)) (Prims.of_int (57)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (614)) (Prims.of_int (14))
                                (Prims.of_int (620)) (Prims.of_int (37)))))
                       (Obj.magic
                          (FStar_Reflection_V2_Formula.term_as_formula
                             (type_of_binding x_t)))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | FStar_Reflection_V2_Formula.Comp
                                 (FStar_Reflection_V2_Formula.Eq uu___1, y,
                                  uu___2)
                                 ->
                                 if FStar_Reflection_V2_Builtins.term_eq x y
                                 then
                                   Obj.magic
                                     (FStar_Tactics_V2_Builtins.rewrite x_t)
                                 else Obj.magic (try_rewrite_equality x bs1)
                             | uu___1 ->
                                 Obj.magic (try_rewrite_equality x bs1))
                            uu___)))) uu___1 uu___
let rec (rewrite_all_context_equalities :
  FStar_Tactics_NamedView.binding Prims.list ->
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
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (627)) (Prims.of_int (8))
                            (Prims.of_int (627)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (628)) (Prims.of_int (8))
                            (Prims.of_int (628)) (Prims.of_int (41)))))
                   (Obj.magic
                      (try_with
                         (fun uu___ ->
                            match () with
                            | () -> FStar_Tactics_V2_Builtins.rewrite x_t)
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (632)) (Prims.of_int (35)) (Prims.of_int (632))
               (Prims.of_int (48)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (632)) (Prims.of_int (4)) (Prims.of_int (632))
               (Prims.of_int (48))))) (Obj.magic (cur_vars ()))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (rewrite_all_context_equalities uu___1))
           uu___1)
let (rewrite_equality :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (635)) (Prims.of_int (27)) (Prims.of_int (635))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (635)) (Prims.of_int (4)) (Prims.of_int (635))
               (Prims.of_int (40))))) (Obj.magic (cur_vars ()))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (try_rewrite_equality t uu___)) uu___)
let (unfold_def :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (638)) (Prims.of_int (10)) (Prims.of_int (638))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (638)) (Prims.of_int (4)) (Prims.of_int (642))
               (Prims.of_int (46)))))
      (Obj.magic (FStar_Tactics_NamedView.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (640)) (Prims.of_int (16))
                                 (Prims.of_int (640)) (Prims.of_int (42)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (641)) (Prims.of_int (8))
                                 (Prims.of_int (641)) (Prims.of_int (30)))))
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              FStar_Reflection_V2_Builtins.implode_qn
                                (FStar_Reflection_V2_Builtins.inspect_fv fv)))
                        (fun uu___1 ->
                           (fun n ->
                              Obj.magic
                                (FStar_Tactics_V2_Builtins.norm
                                   [FStar_Pervasives.delta_fully [n]]))
                             uu___1)))
            | uu___1 ->
                Obj.magic (Obj.repr (fail "unfold_def: term is not a fv")))
           uu___)
let (l_to_r :
  FStar_Tactics_NamedView.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lems ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (649)) (Prims.of_int (8)) (Prims.of_int (652))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (653)) (Prims.of_int (4)) (Prims.of_int (653))
               (Prims.of_int (28)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun uu___1 ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                         (Prims.of_int (649)) (Prims.of_int (8))
                         (Prims.of_int (652)) (Prims.of_int (31)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                         (Prims.of_int (649)) (Prims.of_int (8))
                         (Prims.of_int (652)) (Prims.of_int (31)))))
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
let (mk_squash :
  FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term) =
  fun t ->
    let sq =
      FStar_Tactics_NamedView.pack
        (FStar_Tactics_NamedView.Tv_FVar
           (FStar_Reflection_V2_Builtins.pack_fv
              FStar_Reflection_Const.squash_qn)) in
    FStar_Reflection_V2_Derived.mk_e_app sq [t]
let (mk_sq_eq :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun t1 ->
    fun t2 ->
      let eq =
        FStar_Tactics_NamedView.pack
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) in
      mk_squash (FStar_Reflection_V2_Derived.mk_e_app eq [t1; t2])
let (grewrite :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (666)) (Prims.of_int (12))
                 (Prims.of_int (666)) (Prims.of_int (33)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (666)) (Prims.of_int (36))
                 (Prims.of_int (680)) (Prims.of_int (44)))))
        (Obj.magic (tcut (mk_sq_eq t1 t2)))
        (fun uu___ ->
           (fun e ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (667)) (Prims.of_int (12))
                            (Prims.of_int (667)) (Prims.of_int (27)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (668)) (Prims.of_int (4))
                            (Prims.of_int (680)) (Prims.of_int (44)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         FStar_Tactics_NamedView.pack
                           (FStar_Tactics_NamedView.Tv_Var
                              (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                 e))))
                   (fun uu___ ->
                      (fun e1 ->
                         Obj.magic
                           (pointwise
                              (fun uu___ ->
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (671))
                                            (Prims.of_int (8))
                                            (Prims.of_int (676))
                                            (Prims.of_int (20)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (678))
                                            (Prims.of_int (6))
                                            (Prims.of_int (680))
                                            (Prims.of_int (43)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (671))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (671))
                                                  (Prims.of_int (42)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (671))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (676))
                                                  (Prims.of_int (20)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.V2.Derived.fst"
                                                        (Prims.of_int (671))
                                                        (Prims.of_int (30))
                                                        (Prims.of_int (671))
                                                        (Prims.of_int (42)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.V2.Derived.fst"
                                                        (Prims.of_int (671))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (671))
                                                        (Prims.of_int (42)))))
                                               (Obj.magic (cur_goal ()))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     Obj.magic
                                                       (FStar_Reflection_V2_Formula.term_as_formula
                                                          uu___1)) uu___1)))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               match uu___1 with
                                               | FStar_Reflection_V2_Formula.Comp
                                                   (FStar_Reflection_V2_Formula.Eq
                                                    uu___2, lhs, rhs)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (28)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (24)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_NamedView.inspect
                                                                 lhs))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   match uu___3
                                                                   with
                                                                   | 
                                                                   FStar_Tactics_NamedView.Tv_Uvar
                                                                    (uu___5,
                                                                    uu___6)
                                                                    -> true
                                                                   | 
                                                                   uu___5 ->
                                                                    false))))
                                               | uu___2 ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              false))))
                                              uu___1)))
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
  FStar_Tactics_NamedView.binding ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (687)) (Prims.of_int (8)) (Prims.of_int (687))
               (Prims.of_int (43)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (687)) (Prims.of_int (2)) (Prims.of_int (699))
               (Prims.of_int (7)))))
      (Obj.magic
         (FStar_Reflection_V2_Formula.term_as_formula (type_of_binding b)))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_V2_Formula.Comp
                (FStar_Reflection_V2_Formula.Eq uu___1, l, r) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (689)) (Prims.of_int (4))
                              (Prims.of_int (689)) (Prims.of_int (16)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (690)) (Prims.of_int (4))
                              (Prims.of_int (690)) (Prims.of_int (37)))))
                     (Obj.magic (grewrite l r))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (iseq
                                [idtac;
                                (fun uu___3 ->
                                   exact
                                     (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                        b))])) uu___2))
            | uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (692)) (Prims.of_int (16))
                              (Prims.of_int (692)) (Prims.of_int (52)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (692)) (Prims.of_int (10))
                              (Prims.of_int (698)) (Prims.of_int (56)))))
                     (Obj.magic
                        (FStar_Reflection_V2_Formula.term_as_formula'
                           (type_of_binding b)))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           match uu___2 with
                           | FStar_Reflection_V2_Formula.Comp
                               (FStar_Reflection_V2_Formula.Eq uu___3, l, r)
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Derived.fst"
                                                (Prims.of_int (694))
                                                (Prims.of_int (6))
                                                (Prims.of_int (694))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Derived.fst"
                                                (Prims.of_int (695))
                                                (Prims.of_int (6))
                                                (Prims.of_int (696))
                                                (Prims.of_int (39)))))
                                       (Obj.magic (grewrite l r))
                                       (fun uu___4 ->
                                          (fun uu___4 ->
                                             Obj.magic
                                               (iseq
                                                  [idtac;
                                                  (fun uu___5 ->
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Derived.fst"
                                                                (Prims.of_int (695))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (695))
                                                                (Prims.of_int (55)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Derived.fst"
                                                                (Prims.of_int (696))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (696))
                                                                (Prims.of_int (37)))))
                                                       (Obj.magic
                                                          (apply_lemma
                                                             (FStar_Reflection_V2_Builtins.pack_ln
                                                                (FStar_Reflection_V2_Data.Tv_FVar
                                                                   (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V2";
                                                                    "Derived";
                                                                    "__un_sq_eq"])))))
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             Obj.magic
                                                               (exact
                                                                  (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b)))
                                                            uu___6))]))
                                            uu___4)))
                           | uu___3 ->
                               Obj.magic
                                 (Obj.repr
                                    (fail
                                       "grewrite_eq: binder type is not an equality")))
                          uu___2))) uu___)
let (admit_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (703)) (Prims.of_int (2)) (Prims.of_int (703))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (704)) (Prims.of_int (2)) (Prims.of_int (704))
               (Prims.of_int (16)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.dump "Admitting"))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (apply
                 (FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_FVar
                       (FStar_Reflection_V2_Builtins.pack_fv
                          ["Prims"; "admit"]))))) uu___1)
let admit_dump : 'a . (unit -> 'a) -> unit -> 'a = fun x -> fun uu___ -> x ()
let (magic_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (711)) (Prims.of_int (2)) (Prims.of_int (711))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (712)) (Prims.of_int (2)) (Prims.of_int (714))
               (Prims.of_int (4)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.dump "Admitting"))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (712)) (Prims.of_int (2))
                          (Prims.of_int (712)) (Prims.of_int (16)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (713)) (Prims.of_int (2))
                          (Prims.of_int (714)) (Prims.of_int (4)))))
                 (Obj.magic
                    (apply
                       (FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_FVar
                             (FStar_Reflection_V2_Builtins.pack_fv
                                ["Prims"; "magic"])))))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (713)) (Prims.of_int (2))
                                     (Prims.of_int (713)) (Prims.of_int (13)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (714)) (Prims.of_int (2))
                                     (Prims.of_int (714)) (Prims.of_int (4)))))
                            (Obj.magic
                               (exact
                                  (FStar_Reflection_V2_Builtins.pack_ln
                                     (FStar_Reflection_V2_Data.Tv_Const
                                        FStar_Reflection_V2_Data.C_Unit))))
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> ())))) uu___2))) uu___1)
let magic_dump : 'a . 'a -> unit -> 'a = fun x -> fun uu___ -> x
let (change_with :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      focus
        (fun uu___ ->
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (721)) (Prims.of_int (8))
                      (Prims.of_int (721)) (Prims.of_int (22)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (722)) (Prims.of_int (8))
                      (Prims.of_int (722)) (Prims.of_int (29)))))
             (Obj.magic (grewrite t1 t2))
             (fun uu___1 ->
                (fun uu___1 -> Obj.magic (iseq [idtac; trivial])) uu___1))
let (change_sq :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    FStar_Tactics_V2_Builtins.change
      (FStar_Reflection_V2_Derived.mk_e_app
         (FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_FVar
               (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "squash"])))
         [t1])
let finish_by :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (729)) (Prims.of_int (12)) (Prims.of_int (729))
               (Prims.of_int (16)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (730)) (Prims.of_int (4)) (Prims.of_int (731))
               (Prims.of_int (5))))) (Obj.magic (t ()))
      (fun uu___ ->
         (fun x ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (730)) (Prims.of_int (4))
                          (Prims.of_int (730)) (Prims.of_int (58)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (729)) (Prims.of_int (8))
                          (Prims.of_int (729)) (Prims.of_int (9)))))
                 (Obj.magic
                    (or_else qed
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic (fail "finish_by: not finished"))
                            uu___)))
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
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (734)) (Prims.of_int (4)) (Prims.of_int (734))
                 (Prims.of_int (10)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (734)) (Prims.of_int (11))
                 (Prims.of_int (738)) (Prims.of_int (5)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.dup ()))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (735)) (Prims.of_int (12))
                            (Prims.of_int (735)) (Prims.of_int (42)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (735)) (Prims.of_int (45))
                            (Prims.of_int (738)) (Prims.of_int (5)))))
                   (Obj.magic (focus (fun uu___1 -> finish_by t1)))
                   (fun uu___1 ->
                      (fun x ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (736))
                                       (Prims.of_int (12))
                                       (Prims.of_int (736))
                                       (Prims.of_int (16)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (737))
                                       (Prims.of_int (4))
                                       (Prims.of_int (738))
                                       (Prims.of_int (5)))))
                              (Obj.magic (t2 x))
                              (fun uu___1 ->
                                 (fun y ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (737))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (737))
                                                  (Prims.of_int (12)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (736))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (736))
                                                  (Prims.of_int (9)))))
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
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (741)) (Prims.of_int (4))
                    (Prims.of_int (741)) (Prims.of_int (17)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (742)) (Prims.of_int (4))
                    (Prims.of_int (746)) (Prims.of_int (5)))))
           (Obj.magic
              (apply
                 (FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_FVar
                       (FStar_Reflection_V2_Builtins.pack_fv
                          ["Prims"; "Cons"])))))
           (fun uu___1 ->
              (fun uu___1 ->
                 Obj.magic
                   (focus
                      (fun uu___2 ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (743)) (Prims.of_int (14))
                                    (Prims.of_int (743)) (Prims.of_int (18)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (744)) (Prims.of_int (6))
                                    (Prims.of_int (745)) (Prims.of_int (7)))))
                           (Obj.magic (t ()))
                           (fun uu___3 ->
                              (fun x ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (744))
                                               (Prims.of_int (6))
                                               (Prims.of_int (744))
                                               (Prims.of_int (12)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (743))
                                               (Prims.of_int (10))
                                               (Prims.of_int (743))
                                               (Prims.of_int (11)))))
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
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (765)) (Prims.of_int (42))
                        (Prims.of_int (765)) (Prims.of_int (51)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (765)) (Prims.of_int (36))
                        (Prims.of_int (765)) (Prims.of_int (51)))))
               (FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 ->
                     (fun uu___2 ->
                        Obj.magic
                          (failwith
                             "Cannot evaluate open quotation at runtime"))
                       uu___2))
               (fun uu___2 -> (fun uu___2 -> Obj.magic (exact uu___2)) uu___2))
          (fun uu___1 ->
             FStar_Tactics_V2_Builtins.norm
               [FStar_Pervasives.delta_only l;
               FStar_Pervasives.iota;
               FStar_Pervasives.zeta])
let (tlabel : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (768)) (Prims.of_int (10)) (Prims.of_int (768))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (768)) (Prims.of_int (4)) (Prims.of_int (771))
               (Prims.of_int (38))))) (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] -> Obj.magic (Obj.repr (fail "tlabel: no goals"))
            | h::t ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_V2_Builtins.set_goals
                        ((FStar_Tactics_Types.set_label l h) :: t)))) uu___)
let (tlabel' : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (774)) (Prims.of_int (10)) (Prims.of_int (774))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (774)) (Prims.of_int (4)) (Prims.of_int (778))
               (Prims.of_int (26))))) (Obj.magic (goals ()))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | [] -> Obj.magic (Obj.repr (fail "tlabel': no goals"))
            | h::t ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (777)) (Prims.of_int (16))
                                 (Prims.of_int (777)) (Prims.of_int (45)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (778)) (Prims.of_int (8))
                                 (Prims.of_int (778)) (Prims.of_int (26)))))
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              FStar_Tactics_Types.set_label
                                (Prims.strcat l
                                   (FStar_Tactics_Types.get_label h)) h))
                        (fun uu___1 ->
                           (fun h1 ->
                              Obj.magic
                                (FStar_Tactics_V2_Builtins.set_goals (h1 ::
                                   t))) uu___1)))) uu___)
let (focus_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (781)) (Prims.of_int (4)) (Prims.of_int (781))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (782)) (Prims.of_int (4)) (Prims.of_int (782))
               (Prims.of_int (20)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (781)) (Prims.of_int (14))
                     (Prims.of_int (781)) (Prims.of_int (39)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (781)) (Prims.of_int (4))
                     (Prims.of_int (781)) (Prims.of_int (39)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (781)) (Prims.of_int (15))
                           (Prims.of_int (781)) (Prims.of_int (23)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (781)) (Prims.of_int (14))
                           (Prims.of_int (781)) (Prims.of_int (39)))))
                  (Obj.magic (goals ()))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.Derived.fst"
                                      (Prims.of_int (781))
                                      (Prims.of_int (26))
                                      (Prims.of_int (781))
                                      (Prims.of_int (38)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.Derived.fst"
                                      (Prims.of_int (781))
                                      (Prims.of_int (14))
                                      (Prims.of_int (781))
                                      (Prims.of_int (39)))))
                             (Obj.magic (smt_goals ()))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (op_At ()) uu___1 uu___2))))
                       uu___1)))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic (FStar_Tactics_V2_Builtins.set_goals uu___1))
                 uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_smt_goals [])) uu___1)
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (797)) (Prims.of_int (8)) (Prims.of_int (797))
               (Prims.of_int (38)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (797)) (Prims.of_int (2)) (Prims.of_int (799))
               (Prims.of_int (37)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (797)) (Prims.of_int (28))
                     (Prims.of_int (797)) (Prims.of_int (38)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (797)) (Prims.of_int (8))
                     (Prims.of_int (797)) (Prims.of_int (38)))))
            (Obj.magic (goals ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> extract_nth (n - Prims.int_one) uu___))))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives_Native.None ->
                Obj.magic (Obj.repr (fail "bump_nth: not that many goals"))
            | FStar_Pervasives_Native.Some (h, t) ->
                Obj.magic
                  (Obj.repr (FStar_Tactics_V2_Builtins.set_goals (h :: t))))
           uu___)
let rec (destruct_list :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (802)) (Prims.of_int (21)) (Prims.of_int (802))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (801)) (Prims.of_int (52)) (Prims.of_int (814))
               (Prims.of_int (27)))))
      (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.collect_app t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (head, args) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (803)) (Prims.of_int (10))
                              (Prims.of_int (803)) (Prims.of_int (28)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (803)) (Prims.of_int (4))
                              (Prims.of_int (814)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (803)) (Prims.of_int (10))
                                    (Prims.of_int (803)) (Prims.of_int (22)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (803)) (Prims.of_int (10))
                                    (Prims.of_int (803)) (Prims.of_int (28)))))
                           (Obj.magic (FStar_Tactics_NamedView.inspect head))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> (uu___1, args)))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | (FStar_Tactics_NamedView.Tv_FVar fv,
                              (a1, FStar_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStar_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.cons_qn
                                     then
                                       Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic (destruct_list a2))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 -> a1 :: uu___2)))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_Effect.raise
                                            FStar_Tactics_Common.NotAListLiteral)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv,
                              (uu___2, FStar_Reflection_V2_Data.Q_Implicit)::
                              (a1, FStar_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStar_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.cons_qn
                                     then
                                       Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (807))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic (destruct_list a2))
                                            (fun uu___3 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 -> a1 :: uu___3)))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_Effect.raise
                                            FStar_Tactics_Common.NotAListLiteral)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv, uu___2) ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.nil_qn
                                     then
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> [])
                                     else
                                       FStar_Tactics_Effect.raise
                                         FStar_Tactics_Common.NotAListLiteral))
                           | uu___2 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.raise
                                       FStar_Tactics_Common.NotAListLiteral)))
                          uu___1))) uu___)
let (get_match_body :
  unit -> (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (817)) (Prims.of_int (8)) (Prims.of_int (817))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (817)) (Prims.of_int (2)) (Prims.of_int (821))
               (Prims.of_int (46)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (817)) (Prims.of_int (22))
                     (Prims.of_int (817)) (Prims.of_int (35)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                     (Prims.of_int (817)) (Prims.of_int (8))
                     (Prims.of_int (817)) (Prims.of_int (35)))))
            (Obj.magic (cur_goal ()))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    FStar_Reflection_V2_Derived.unsquash_term uu___1))))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Pervasives_Native.None -> Obj.magic (Obj.repr (fail ""))
            | FStar_Pervasives_Native.Some t ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (819)) (Prims.of_int (20))
                                 (Prims.of_int (819)) (Prims.of_int (39)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (819)) (Prims.of_int (14))
                                 (Prims.of_int (821)) (Prims.of_int (46)))))
                        (Obj.magic
                           (FStar_Tactics_V2_SyntaxHelpers.inspect_unascribe
                              t))
                        (fun uu___2 ->
                           match uu___2 with
                           | FStar_Tactics_NamedView.Tv_Match
                               (sc, uu___3, uu___4) ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 -> sc)
                           | uu___3 -> fail "Goal is not a match")))) uu___1)
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
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (834)) (Prims.of_int (14))
                    (Prims.of_int (834)) (Prims.of_int (31)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (834)) (Prims.of_int (34))
                    (Prims.of_int (840)) (Prims.of_int (20)))))
           (Obj.magic (get_match_body ()))
           (fun uu___2 ->
              (fun x ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Derived.fst"
                               (Prims.of_int (835)) (Prims.of_int (14))
                               (Prims.of_int (835)) (Prims.of_int (26)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Derived.fst"
                               (Prims.of_int (836)) (Prims.of_int (6))
                               (Prims.of_int (840)) (Prims.of_int (20)))))
                      (Obj.magic (FStar_Tactics_V2_Builtins.t_destruct x))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            Obj.magic
                              (iterAll
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (837))
                                               (Prims.of_int (17))
                                               (Prims.of_int (837))
                                               (Prims.of_int (29)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (837))
                                               (Prims.of_int (32))
                                               (Prims.of_int (840))
                                               (Prims.of_int (19)))))
                                      (Obj.magic
                                         (repeat
                                            FStar_Tactics_V2_Builtins.intro))
                                      (fun uu___4 ->
                                         (fun bs ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.V2.Derived.fst"
                                                          (Prims.of_int (838))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (838))
                                                          (Prims.of_int (23)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.V2.Derived.fst"
                                                          (Prims.of_int (839))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (840))
                                                          (Prims.of_int (19)))))
                                                 (Obj.magic (last bs))
                                                 (fun uu___4 ->
                                                    (fun b ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (21)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (19)))))
                                                            (Obj.magic
                                                               (grewrite_eq b))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Builtins.norm
                                                                    [FStar_Pervasives.iota]))
                                                                 uu___4)))
                                                      uu___4))) uu___4))))
                           uu___2))) uu___2))
let (nth_var :
  Prims.int ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun i ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (849)) (Prims.of_int (11)) (Prims.of_int (849))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (849)) (Prims.of_int (25)) (Prims.of_int (854))
               (Prims.of_int (15))))) (Obj.magic (cur_vars ()))
      (fun uu___ ->
         (fun bs ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (850)) (Prims.of_int (16))
                          (Prims.of_int (850)) (Prims.of_int (65)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (850)) (Prims.of_int (68))
                          (Prims.of_int (854)) (Prims.of_int (15)))))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       if i >= Prims.int_zero
                       then i
                       else (FStar_List_Tot_Base.length bs) + i))
                 (fun uu___ ->
                    (fun k ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (851)) (Prims.of_int (16))
                                     (Prims.of_int (851)) (Prims.of_int (62)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (852)) (Prims.of_int (2))
                                     (Prims.of_int (854)) (Prims.of_int (15)))))
                            (if k < Prims.int_zero
                             then fail "not enough binders"
                             else
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 -> k))
                            (fun k1 ->
                               match FStar_List_Tot_Base.nth bs k1 with
                               | FStar_Pervasives_Native.None ->
                                   fail "not enough binders"
                               | FStar_Pervasives_Native.Some b ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> b)))) uu___))) uu___)
exception Appears 
let (uu___is_Appears : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Appears -> true | uu___ -> false
let (name_appears_in :
  FStar_Reflection_Types.name ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (862)) (Prims.of_int (4)) (Prims.of_int (867))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (869)) (Prims.of_int (2)) (Prims.of_int (871))
                 (Prims.of_int (16)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (862)) (Prims.of_int (10))
                           (Prims.of_int (862)) (Prims.of_int (19)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (862)) (Prims.of_int (4))
                           (Prims.of_int (867)) (Prims.of_int (19)))))
                  (Obj.magic (FStar_Tactics_NamedView.inspect t1))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Tactics_NamedView.Tv_FVar fv ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (864))
                                             (Prims.of_int (6))
                                             (Prims.of_int (865))
                                             (Prims.of_int (21)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (861))
                                             (Prims.of_int (10))
                                             (Prims.of_int (861))
                                             (Prims.of_int (11)))))
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = nm
                                     then FStar_Tactics_Effect.raise Appears
                                     else
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> ()))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> t1))))
                        | tv ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Tactics_NamedView.pack tv))))
                       uu___1)))
        (fun uu___ ->
           (fun ff ->
              Obj.magic
                (try_with
                   (fun uu___ ->
                      match () with
                      | () ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (869)) (Prims.of_int (6))
                                     (Prims.of_int (869)) (Prims.of_int (30)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (869)) (Prims.of_int (32))
                                     (Prims.of_int (869)) (Prims.of_int (37)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V2.Derived.fst"
                                           (Prims.of_int (869))
                                           (Prims.of_int (13))
                                           (Prims.of_int (869))
                                           (Prims.of_int (30)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V2.Derived.fst"
                                           (Prims.of_int (869))
                                           (Prims.of_int (6))
                                           (Prims.of_int (869))
                                           (Prims.of_int (30)))))
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
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 -> true))
                         | e -> Obj.magic (FStar_Tactics_Effect.raise e))
                        uu___))) uu___)
let rec (mk_abs :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
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
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (878)) (Prims.of_int (13))
                                (Prims.of_int (878)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range " dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic (mk_abs args' t))
                       (fun t' ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Tactics_NamedView.pack
                                 (FStar_Tactics_NamedView.Tv_Abs (a, t')))))))
        uu___1 uu___
let (namedv_to_simple_binder :
  FStar_Tactics_NamedView.namedv ->
    (FStar_Tactics_NamedView.simple_binder, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun n ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (883)) (Prims.of_int (11)) (Prims.of_int (883))
               (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (885)) (Prims.of_int (4)) (Prims.of_int (889))
               (Prims.of_int (16)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Tactics_NamedView.inspect_namedv n))
      (fun uu___ ->
         (fun nv ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (887)) (Prims.of_int (13))
                          (Prims.of_int (887)) (Prims.of_int (27)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (885)) (Prims.of_int (4))
                          (Prims.of_int (889)) (Prims.of_int (16)))))
                 (Obj.magic
                    (FStar_Tactics_Unseal.unseal
                       nv.FStar_Reflection_V2_Data.sort))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         {
                           FStar_Tactics_NamedView.uniq =
                             (nv.FStar_Reflection_V2_Data.uniq);
                           FStar_Tactics_NamedView.ppname =
                             (nv.FStar_Reflection_V2_Data.ppname);
                           FStar_Tactics_NamedView.sort = uu___;
                           FStar_Tactics_NamedView.qual =
                             FStar_Reflection_V2_Data.Q_Explicit;
                           FStar_Tactics_NamedView.attrs = []
                         })))) uu___)
let (binding_to_simple_binder :
  FStar_Tactics_NamedView.binding -> FStar_Tactics_NamedView.simple_binder) =
  fun b ->
    {
      FStar_Tactics_NamedView.uniq = (b.FStar_Reflection_V2_Data.uniq1);
      FStar_Tactics_NamedView.ppname = (b.FStar_Reflection_V2_Data.ppname3);
      FStar_Tactics_NamedView.sort = (b.FStar_Reflection_V2_Data.sort3);
      FStar_Tactics_NamedView.qual = FStar_Reflection_V2_Data.Q_Explicit;
      FStar_Tactics_NamedView.attrs = []
    }
let (string_to_term_with_lb :
  (Prims.string * FStar_Tactics_NamedView.term) Prims.list ->
    FStar_Reflection_Types.env ->
      Prims.string ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun letbindings ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (909)) (Prims.of_int (6))
                   (Prims.of_int (912)) (Prims.of_int (27)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (908)) (Prims.of_int (3))
                   (Prims.of_int (916)) (Prims.of_int (21)))))
          (Obj.magic
             (FStar_Tactics_Util.fold_left
                (fun uu___ ->
                   fun uu___1 ->
                     match (uu___, uu___1) with
                     | ((e1, lb_bvs), (i, v)) ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (910)) (Prims.of_int (19))
                                    (Prims.of_int (910)) (Prims.of_int (36)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (909)) (Prims.of_int (42))
                                    (Prims.of_int (911)) (Prims.of_int (25)))))
                           (Obj.magic
                              (FStar_Tactics_V2_Builtins.push_bv_dsenv e1 i))
                           (fun uu___2 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   match uu___2 with
                                   | (e2, b) -> (e2, ((v, b) :: lb_bvs)))))
                (e, []) letbindings))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (e1, lb_bindings) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (912)) (Prims.of_int (30))
                                  (Prims.of_int (916)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (912)) (Prims.of_int (30))
                                  (Prims.of_int (916)) (Prims.of_int (21)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> uu___))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (913))
                                             (Prims.of_int (12))
                                             (Prims.of_int (913))
                                             (Prims.of_int (30)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (914))
                                             (Prims.of_int (4))
                                             (Prims.of_int (916))
                                             (Prims.of_int (21)))))
                                    (Obj.magic
                                       (FStar_Tactics_V2_Builtins.string_to_term
                                          e1 t))
                                    (fun uu___2 ->
                                       (fun t1 ->
                                          Obj.magic
                                            (FStar_Tactics_Util.fold_left
                                               (fun uu___3 ->
                                                  fun uu___2 ->
                                                    (fun t2 ->
                                                       fun uu___2 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 match uu___2
                                                                 with
                                                                 | (i, b) ->
                                                                    FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Let
                                                                    (false,
                                                                    [],
                                                                    (binding_to_simple_binder
                                                                    b), i,
                                                                    t2)))))
                                                      uu___3 uu___2) t1
                                               lb_bindings)) uu___2))) uu___1)))
               uu___)
let (trans : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    apply_lemma
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V2"; "Derived"; "lem_trans"])))
let (smt_sync : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (928)) (Prims.of_int (40)) (Prims.of_int (928))
               (Prims.of_int (56)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (928)) (Prims.of_int (29)) (Prims.of_int (928))
               (Prims.of_int (56)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Tactics_V2_Builtins.t_smt_sync uu___1)) uu___1)
let (smt_sync' :
  Prims.nat -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun fuel ->
    fun ifuel ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (932)) (Prims.of_int (15))
                 (Prims.of_int (932)) (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (932)) (Prims.of_int (32))
                 (Prims.of_int (936)) (Prims.of_int (20)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
        (fun uu___ ->
           (fun vcfg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (933)) (Prims.of_int (18))
                            (Prims.of_int (934)) (Prims.of_int (68)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (936)) (Prims.of_int (4))
                            (Prims.of_int (936)) (Prims.of_int (20)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         {
                           FStar_VConfig.initial_fuel = fuel;
                           FStar_VConfig.max_fuel = fuel;
                           FStar_VConfig.initial_ifuel = ifuel;
                           FStar_VConfig.max_ifuel = ifuel;
                           FStar_VConfig.detail_errors =
                             (vcfg.FStar_VConfig.detail_errors);
                           FStar_VConfig.detail_hint_replay =
                             (vcfg.FStar_VConfig.detail_hint_replay);
                           FStar_VConfig.no_smt = (vcfg.FStar_VConfig.no_smt);
                           FStar_VConfig.quake_lo =
                             (vcfg.FStar_VConfig.quake_lo);
                           FStar_VConfig.quake_hi =
                             (vcfg.FStar_VConfig.quake_hi);
                           FStar_VConfig.quake_keep =
                             (vcfg.FStar_VConfig.quake_keep);
                           FStar_VConfig.retry = (vcfg.FStar_VConfig.retry);
                           FStar_VConfig.smtencoding_elim_box =
                             (vcfg.FStar_VConfig.smtencoding_elim_box);
                           FStar_VConfig.smtencoding_nl_arith_repr =
                             (vcfg.FStar_VConfig.smtencoding_nl_arith_repr);
                           FStar_VConfig.smtencoding_l_arith_repr =
                             (vcfg.FStar_VConfig.smtencoding_l_arith_repr);
                           FStar_VConfig.smtencoding_valid_intro =
                             (vcfg.FStar_VConfig.smtencoding_valid_intro);
                           FStar_VConfig.smtencoding_valid_elim =
                             (vcfg.FStar_VConfig.smtencoding_valid_elim);
                           FStar_VConfig.tcnorm = (vcfg.FStar_VConfig.tcnorm);
                           FStar_VConfig.no_plugins =
                             (vcfg.FStar_VConfig.no_plugins);
                           FStar_VConfig.no_tactics =
                             (vcfg.FStar_VConfig.no_tactics);
                           FStar_VConfig.z3cliopt =
                             (vcfg.FStar_VConfig.z3cliopt);
                           FStar_VConfig.z3smtopt =
                             (vcfg.FStar_VConfig.z3smtopt);
                           FStar_VConfig.z3refresh =
                             (vcfg.FStar_VConfig.z3refresh);
                           FStar_VConfig.z3rlimit =
                             (vcfg.FStar_VConfig.z3rlimit);
                           FStar_VConfig.z3rlimit_factor =
                             (vcfg.FStar_VConfig.z3rlimit_factor);
                           FStar_VConfig.z3seed = (vcfg.FStar_VConfig.z3seed);
                           FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                             =
                             (vcfg.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                           FStar_VConfig.reuse_hint_for =
                             (vcfg.FStar_VConfig.reuse_hint_for)
                         }))
                   (fun uu___ ->
                      (fun vcfg' ->
                         Obj.magic
                           (FStar_Tactics_V2_Builtins.t_smt_sync vcfg'))
                        uu___))) uu___)