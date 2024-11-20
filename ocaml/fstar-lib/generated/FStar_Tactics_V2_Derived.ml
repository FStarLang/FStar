open Prims
let op_At :
  'uuuuu .
    unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list
  = fun uu___ -> FStar_List_Tot_Base.op_At
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let (name_of_bv :
  FStar_Tactics_NamedView.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    FStarC_Tactics_Unseal.unseal
      (FStar_Tactics_NamedView.inspect_bv bv).FStarC_Reflection_V2_Data.ppname1
let (bv_to_string :
  FStar_Tactics_NamedView.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun bv -> name_of_bv bv
let (name_of_binder :
  FStar_Tactics_NamedView.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> FStarC_Tactics_Unseal.unseal b.FStar_Tactics_NamedView.ppname
let (binder_to_string :
  FStar_Tactics_NamedView.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ = name_of_binder b in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (50)) (Prims.of_int (2)) (Prims.of_int (50))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (50)) (Prims.of_int (2)) (Prims.of_int (50))
               (Prims.of_int (86))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_Tactics_V2_Builtins.term_to_string
                        b.FStar_Tactics_NamedView.sort in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Derived.fst"
                               (Prims.of_int (50)) (Prims.of_int (59))
                               (Prims.of_int (50)) (Prims.of_int (80)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___6)
                      (fun uu___7 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___8 -> Prims.strcat uu___7 ")")) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (50)) (Prims.of_int (59))
                             (Prims.of_int (50)) (Prims.of_int (86)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___5)
                    (fun uu___6 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___7 -> Prims.strcat "::(" uu___6)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (50)) (Prims.of_int (51))
                           (Prims.of_int (50)) (Prims.of_int (86)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Prims.fst"
                           (Prims.of_int (611)) (Prims.of_int (19))
                           (Prims.of_int (611)) (Prims.of_int (31)))))
                  (Obj.magic uu___4)
                  (fun uu___5 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___6 ->
                          Prims.strcat
                            (Prims.string_of_int
                               b.FStar_Tactics_NamedView.uniq) uu___5)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                         (Prims.of_int (50)) (Prims.of_int (28))
                         (Prims.of_int (50)) (Prims.of_int (86)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___3)
                (fun uu___4 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___5 -> Prims.strcat "@@" uu___4)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (50)) (Prims.of_int (21))
                          (Prims.of_int (50)) (Prims.of_int (86)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 -> Prims.strcat uu___1 uu___3)))) uu___1)
let (binding_to_string :
  FStar_Tactics_NamedView.binding ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> FStarC_Tactics_Unseal.unseal b.FStarC_Reflection_V2_Data.ppname3
let (type_of_var :
  FStar_Tactics_NamedView.namedv ->
    (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    FStarC_Tactics_Unseal.unseal
      (FStar_Tactics_NamedView.inspect_namedv x).FStarC_Reflection_V2_Data.sort
let (type_of_binding :
  FStar_Tactics_NamedView.binding -> FStarC_Reflection_Types.typ) =
  fun x -> x.FStarC_Reflection_V2_Data.sort3
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (63)) (Prims.of_int (42)) (Prims.of_int (63))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (63)) (Prims.of_int (33)) (Prims.of_int (63))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (64)) (Prims.of_int (50)) (Prims.of_int (64))
               (Prims.of_int (58)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (64)) (Prims.of_int (37)) (Prims.of_int (64))
               (Prims.of_int (58))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.smt_goals_of uu___2))
let fail_doc_at :
  'a .
    FStarC_Errors_Msg.error_message ->
      FStar_Range.range FStar_Pervasives_Native.option ->
        ('a, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    fun r ->
      FStar_Tactics_Effect.raise (FStarC_Tactics_Common.TacticFailure (m, r))
let fail_doc :
  'a .
    FStarC_Errors_Msg.error_message ->
      ('a, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    FStar_Tactics_Effect.raise
      (FStarC_Tactics_Common.TacticFailure (m, FStar_Pervasives_Native.None))
let fail_at :
  'a .
    Prims.string ->
      FStar_Range.range FStar_Pervasives_Native.option ->
        ('a, Obj.t) FStar_Tactics_Effect.tac_repr
  = fun m -> fun r -> fail_doc_at (FStarC_Errors_Msg.mkmsg m) r
let fail : 'a . Prims.string -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr =
  fun m -> fail_at m FStar_Pervasives_Native.None
let fail_silently_doc :
  'a .
    FStarC_Errors_Msg.error_message ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.set_urgency Prims.int_zero in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (84)) (Prims.of_int (4)) (Prims.of_int (84))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (85)) (Prims.of_int (4)) (Prims.of_int (85))
               (Prims.of_int (38))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.raise
           (FStarC_Tactics_Common.TacticFailure
              (m, FStar_Pervasives_Native.None)))
let fail_silently :
  'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun m -> fail_silently_doc (FStarC_Errors_Msg.mkmsg m)
let (_cur_goal :
  unit -> (FStarC_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (93)) (Prims.of_int (10)) (Prims.of_int (93))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (93)) (Prims.of_int (4)) (Prims.of_int (95))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (98)) (Prims.of_int (36)) (Prims.of_int (98))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (98)) (Prims.of_int (27)) (Prims.of_int (98))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (101)) (Prims.of_int (38)) (Prims.of_int (101))
               (Prims.of_int (52)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (101)) (Prims.of_int (28)) (Prims.of_int (101))
               (Prims.of_int (52))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Tactics_Types.goal_type uu___2))
let (cur_witness :
  unit -> (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = _cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (104)) (Prims.of_int (45)) (Prims.of_int (104))
               (Prims.of_int (59)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (104)) (Prims.of_int (32)) (Prims.of_int (104))
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
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (111)) (Prims.of_int (18))
                 (Prims.of_int (111)) (Prims.of_int (26)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (111)) (Prims.of_int (9)) (Prims.of_int (111))
                 (Prims.of_int (26))))) (Obj.magic uu___2)
        (fun uu___3 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___4 -> FStarC_Tactics_Types.goals_of uu___3)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (111)) (Prims.of_int (9)) (Prims.of_int (111))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (111)) (Prims.of_int (3)) (Prims.of_int (112))
               (Prims.of_int (16))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> match uu___2 with | g::uu___4 -> g))
let (cur_vars :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = cur_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (115)) (Prims.of_int (16)) (Prims.of_int (115))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (115)) (Prims.of_int (4)) (Prims.of_int (115))
               (Prims.of_int (28))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Reflection_V2_Builtins.vars_of_env uu___2))
let with_policy :
  'a .
    FStarC_Tactics_Types.guard_policy ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun pol ->
    fun f ->
      let uu___ = FStarC_Tactics_V2_Builtins.get_guard_policy () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (119)) (Prims.of_int (18))
                 (Prims.of_int (119)) (Prims.of_int (37)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (120)) (Prims.of_int (4)) (Prims.of_int (123))
                 (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun old_pol ->
              let uu___1 = FStarC_Tactics_V2_Builtins.set_guard_policy pol in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (120)) (Prims.of_int (4))
                            (Prims.of_int (120)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (120)) (Prims.of_int (25))
                            (Prims.of_int (123)) (Prims.of_int (5)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___3 = f () in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (121))
                                       (Prims.of_int (12))
                                       (Prims.of_int (121))
                                       (Prims.of_int (16)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (122))
                                       (Prims.of_int (4))
                                       (Prims.of_int (123))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun r ->
                                    let uu___4 =
                                      FStarC_Tactics_V2_Builtins.set_guard_policy
                                        old_pol in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (122))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (122))
                                                  (Prims.of_int (28)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (121))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (121))
                                                  (Prims.of_int (9)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 -> r)))) uu___4)))
                        uu___2))) uu___1)
let (exact :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStarC_Tactics_Types.SMT
      (fun uu___ -> FStarC_Tactics_V2_Builtins.t_exact true false t)
let (exact_with_ref :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStarC_Tactics_Types.SMT
      (fun uu___ -> FStarC_Tactics_V2_Builtins.t_exact true true t)
let (trivial : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStarC_Tactics_V2_Builtins.norm
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (137)) (Prims.of_int (2)) (Prims.of_int (137))
               (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (137)) (Prims.of_int (62)) (Prims.of_int (141))
               (Prims.of_int (31))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = cur_goal () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (138)) (Prims.of_int (10))
                          (Prims.of_int (138)) (Prims.of_int (21)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (139)) (Prims.of_int (2))
                          (Prims.of_int (141)) (Prims.of_int (31)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun g ->
                       let uu___4 =
                         FStar_Reflection_V2_Formula.term_as_formula g in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (139)) (Prims.of_int (8))
                                     (Prims.of_int (139)) (Prims.of_int (25)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (139)) (Prims.of_int (2))
                                     (Prims.of_int (141)) (Prims.of_int (31)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  match uu___5 with
                                  | FStar_Reflection_V2_Formula.True_ ->
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (153)) (Prims.of_int (10)) (Prims.of_int (153))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (153)) (Prims.of_int (4)) (Prims.of_int (155))
               (Prims.of_int (27))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | [] -> Obj.magic (Obj.repr (fail "dismiss: no more goals"))
            | uu___3::gs ->
                Obj.magic
                  (Obj.repr (FStarC_Tactics_V2_Builtins.set_goals gs)))
           uu___2)
let (flip : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (159)) (Prims.of_int (13)) (Prims.of_int (159))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (160)) (Prims.of_int (4)) (Prims.of_int (162))
               (Prims.of_int (42))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun gs ->
            let uu___2 = goals () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (160)) (Prims.of_int (10))
                          (Prims.of_int (160)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (160)) (Prims.of_int (4))
                          (Prims.of_int (162)) (Prims.of_int (42)))))
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
                                (FStarC_Tactics_V2_Builtins.set_goals (g2 ::
                                   g1 :: gs1)))) uu___3))) uu___2)
let (qed : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (166)) (Prims.of_int (10)) (Prims.of_int (166))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (166)) (Prims.of_int (4)) (Prims.of_int (168))
               (Prims.of_int (32))))) (Obj.magic uu___1)
      (fun uu___2 ->
         match uu___2 with
         | [] -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ())
         | uu___3 -> fail "qed: not done!")
let (debug : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (173)) (Prims.of_int (7)) (Prims.of_int (173))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (173)) (Prims.of_int (4)) (Prims.of_int (173))
               (Prims.of_int (32))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (FStarC_Tactics_V2_Builtins.print m))
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
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (180)) (Prims.of_int (10))
                 (Prims.of_int (180)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (180)) (Prims.of_int (10))
                 (Prims.of_int (180)) (Prims.of_int (32)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___4 = smt_goals () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (180)) (Prims.of_int (20))
                            (Prims.of_int (180)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (180)) (Prims.of_int (10))
                            (Prims.of_int (180)) (Prims.of_int (32)))))
                   (Obj.magic uu___4)
                   (fun uu___5 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___6 -> (uu___3, uu___5))))) uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (180)) (Prims.of_int (10)) (Prims.of_int (180))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (180)) (Prims.of_int (4)) (Prims.of_int (186))
               (Prims.of_int (11))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | ([], uu___3) ->
                Obj.magic (Obj.repr (fail "smt: no active goals"))
            | (g::gs, gs') ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 = FStarC_Tactics_V2_Builtins.set_goals gs in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (184)) (Prims.of_int (8))
                                 (Prims.of_int (184)) (Prims.of_int (20)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (185)) (Prims.of_int (8))
                                 (Prims.of_int (185)) (Prims.of_int (32)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              Obj.magic
                                (FStarC_Tactics_V2_Builtins.set_smt_goals (g
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (192)) (Prims.of_int (10)) (Prims.of_int (192))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (192)) (Prims.of_int (4)) (Prims.of_int (194))
               (Prims.of_int (33))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | g::gs ->
                Obj.magic
                  (Obj.repr
                     (FStarC_Tactics_V2_Builtins.set_goals
                        ((op_At ()) gs [g])))
            | uu___3 -> Obj.magic (Obj.repr (fail "later: no goals"))) uu___2)
let (apply :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V2_Builtins.t_apply true false false t
let (apply_noinst :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V2_Builtins.t_apply true true false t
let (apply_lemma :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V2_Builtins.t_apply_lemma false false t
let (trefl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V2_Builtins.t_trefl false
let (trefl_guard : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V2_Builtins.t_trefl true
let (commute_applied_match :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V2_Builtins.t_commute_applied_match ()
let (apply_lemma_noinst :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V2_Builtins.t_apply_lemma true false t
let (apply_lemma_rw :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V2_Builtins.t_apply_lemma false true t
let (apply_raw :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStarC_Tactics_V2_Builtins.t_apply false false false t
let (exact_guard :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    with_policy FStarC_Tactics_Types.Goal
      (fun uu___ -> FStarC_Tactics_V2_Builtins.t_exact true false t)
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
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (253)) (Prims.of_int (4)) (Prims.of_int (253))
                 (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (254)) (Prims.of_int (4)) (Prims.of_int (258))
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
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (256)) (Prims.of_int (4))
                            (Prims.of_int (256)) (Prims.of_int (10)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (258)) (Prims.of_int (2))
                            (Prims.of_int (258)) (Prims.of_int (24)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun rw ->
                         Obj.magic
                           (FStarC_Tactics_V2_Builtins.ctrl_rewrite d ctrl rw))
                        uu___2))) uu___1)
let (topdown_rewrite :
  (FStar_Tactics_NamedView.term ->
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
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (283)) (Prims.of_int (17))
                             (Prims.of_int (283)) (Prims.of_int (23)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (282)) (Prims.of_int (49))
                             (Prims.of_int (291)) (Prims.of_int (10)))))
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
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (285))
                                            (Prims.of_int (8))
                                            (Prims.of_int (289))
                                            (Prims.of_int (58)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (291))
                                            (Prims.of_int (6))
                                            (Prims.of_int (291))
                                            (Prims.of_int (10)))))
                                   (Obj.magic uu___4)
                                   (fun f ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> (b, f))))) uu___3))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (282)) (Prims.of_int (49))
                 (Prims.of_int (291)) (Prims.of_int (10)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (293)) (Prims.of_int (4)) (Prims.of_int (293))
                 (Prims.of_int (33))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun ctrl' ->
              Obj.magic
                (FStarC_Tactics_V2_Builtins.ctrl_rewrite
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
    let uu___1 = FStarC_Tactics_V2_Builtins.top_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (299)) (Prims.of_int (13)) (Prims.of_int (299))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (299)) (Prims.of_int (4)) (Prims.of_int (299))
               (Prims.of_int (25))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStarC_Reflection_V2_Builtins.moduleof uu___2))
let (open_modules :
  unit ->
    (FStarC_Reflection_Types.name Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.top_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (302)) (Prims.of_int (21)) (Prims.of_int (302))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (302)) (Prims.of_int (4)) (Prims.of_int (302))
               (Prims.of_int (33))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 ->
              FStarC_Reflection_V2_Builtins.env_open_modules uu___2))
let (fresh_uvar :
  FStarC_Reflection_Types.typ FStar_Pervasives_Native.option ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    let uu___ = cur_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (305)) (Prims.of_int (12)) (Prims.of_int (305))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (306)) (Prims.of_int (4)) (Prims.of_int (306))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun e -> Obj.magic (FStarC_Tactics_V2_Builtins.uvar_env e o))
           uu___1)
let (unify :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (309)) (Prims.of_int (12))
                 (Prims.of_int (309)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (310)) (Prims.of_int (4)) (Prims.of_int (310))
                 (Prims.of_int (21))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e -> Obj.magic (FStarC_Tactics_V2_Builtins.unify_env e t1 t2))
             uu___1)
let (unify_guard :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (313)) (Prims.of_int (12))
                 (Prims.of_int (313)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (314)) (Prims.of_int (4)) (Prims.of_int (314))
                 (Prims.of_int (27))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              Obj.magic (FStarC_Tactics_V2_Builtins.unify_guard_env e t1 t2))
             uu___1)
let (tmatch :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (317)) (Prims.of_int (12))
                 (Prims.of_int (317)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (318)) (Prims.of_int (4)) (Prims.of_int (318))
                 (Prims.of_int (21))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e -> Obj.magic (FStarC_Tactics_V2_Builtins.match_env e t1 t2))
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
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (324)) (Prims.of_int (4))
                   (Prims.of_int (325)) (Prims.of_int (31)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (325)) (Prims.of_int (32))
                   (Prims.of_int (338)) (Prims.of_int (10)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = goals () in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (326)) (Prims.of_int (18))
                             (Prims.of_int (326)) (Prims.of_int (26)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (326)) (Prims.of_int (18))
                             (Prims.of_int (326)) (Prims.of_int (40)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          let uu___5 = smt_goals () in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.V2.Derived.fst"
                                        (Prims.of_int (326))
                                        (Prims.of_int (28))
                                        (Prims.of_int (326))
                                        (Prims.of_int (40)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.V2.Derived.fst"
                                        (Prims.of_int (326))
                                        (Prims.of_int (18))
                                        (Prims.of_int (326))
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
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (326)) (Prims.of_int (18))
                              (Prims.of_int (326)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (325)) (Prims.of_int (32))
                              (Prims.of_int (338)) (Prims.of_int (10)))))
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
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (327))
                                             (Prims.of_int (19))
                                             (Prims.of_int (327))
                                             (Prims.of_int (45)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (326))
                                             (Prims.of_int (43))
                                             (Prims.of_int (338))
                                             (Prims.of_int (10)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | (gs1, gs2) ->
                                              let uu___6 =
                                                FStarC_Tactics_V2_Builtins.set_goals
                                                  gs1 in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.V2.Derived.fst"
                                                            (Prims.of_int (329))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (329))
                                                            (Prims.of_int (17)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.V2.Derived.fst"
                                                            (Prims.of_int (329))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (338))
                                                            (Prims.of_int (10)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      (fun uu___7 ->
                                                         let uu___8 =
                                                           FStarC_Tactics_V2_Builtins.set_smt_goals
                                                             [] in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (338))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (338))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (331))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (331))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (338))
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
                                                                    FStarC_Tactics_V2_Builtins.set_goals
                                                                    gs2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (338))
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
                                                                    FStarC_Tactics_V2_Builtins.set_smt_goals
                                                                    [] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (338))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (338))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (335))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (335))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (338))
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
                                                                    FStarC_Tactics_V2_Builtins.set_goals
                                                                    ((op_At
                                                                    ()) gsl
                                                                    gsr) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (338))
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
                                                                    FStarC_Tactics_V2_Builtins.set_smt_goals
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (338))
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
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (342)) (Prims.of_int (23))
                            (Prims.of_int (342)) (Prims.of_int (53)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (342)) (Prims.of_int (57))
                            (Prims.of_int (342)) (Prims.of_int (59)))))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (348)) (Prims.of_int (10)) (Prims.of_int (348))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (348)) (Prims.of_int (4)) (Prims.of_int (355))
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
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (351)) (Prims.of_int (18))
                                 (Prims.of_int (351)) (Prims.of_int (30)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (352)) (Prims.of_int (8))
                                 (Prims.of_int (355)) (Prims.of_int (9)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun sgs ->
                              let uu___3 =
                                FStarC_Tactics_V2_Builtins.set_goals [g] in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (352))
                                            (Prims.of_int (8))
                                            (Prims.of_int (352))
                                            (Prims.of_int (21)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (352))
                                            (Prims.of_int (23))
                                            (Prims.of_int (355))
                                            (Prims.of_int (9)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         let uu___5 =
                                           FStarC_Tactics_V2_Builtins.set_smt_goals
                                             [] in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (352))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (352))
                                                       (Prims.of_int (39)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (352))
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (355))
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
                                                                  "FStar.Tactics.V2.Derived.fst"
                                                                  (Prims.of_int (353))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (353))
                                                                  (Prims.of_int (20)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Derived.fst"
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (355))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (354))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (33)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (354))
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
                                                                    (FStarC_Tactics_V2_Builtins.set_goals
                                                                    uu___10))
                                                                    uu___10) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (355))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (354))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (354))
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
                                                                    (FStarC_Tactics_V2_Builtins.set_smt_goals
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (353))
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
  fun m -> focus (fun uu___ -> FStarC_Tactics_V2_Builtins.dump m)
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (361)) (Prims.of_int (10)) (Prims.of_int (361))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (361)) (Prims.of_int (4)) (Prims.of_int (363))
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
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (363)) (Prims.of_int (27))
                                 (Prims.of_int (363)) (Prims.of_int (58)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (363)) (Prims.of_int (13))
                                 (Prims.of_int (363)) (Prims.of_int (66)))))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (367)) (Prims.of_int (10)) (Prims.of_int (367))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (367)) (Prims.of_int (4)) (Prims.of_int (369))
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
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (369)) (Prims.of_int (22))
                                 (Prims.of_int (369)) (Prims.of_int (54)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (369)) (Prims.of_int (58))
                                 (Prims.of_int (369)) (Prims.of_int (60)))))
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
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (372)) (Prims.of_int (18))
                 (Prims.of_int (372)) (Prims.of_int (26)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (372)) (Prims.of_int (18))
                 (Prims.of_int (372)) (Prims.of_int (40)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___3 = smt_goals () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (372)) (Prims.of_int (28))
                            (Prims.of_int (372)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (372)) (Prims.of_int (18))
                            (Prims.of_int (372)) (Prims.of_int (40)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> (uu___2, uu___4))))) uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (372)) (Prims.of_int (18)) (Prims.of_int (372))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (371)) (Prims.of_int (50)) (Prims.of_int (378))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (gs, sgs) ->
                let uu___2 = FStarC_Tactics_V2_Builtins.set_goals sgs in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (373)) (Prims.of_int (4))
                              (Prims.of_int (373)) (Prims.of_int (17)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (374)) (Prims.of_int (4))
                              (Prims.of_int (378)) (Prims.of_int (28)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 =
                             FStarC_Tactics_V2_Builtins.set_smt_goals [] in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (374))
                                         (Prims.of_int (4))
                                         (Prims.of_int (374))
                                         (Prims.of_int (20)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (375))
                                         (Prims.of_int (4))
                                         (Prims.of_int (378))
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
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (375))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (375))
                                                    (Prims.of_int (13)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (375))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (378))
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
                                                              "FStar.Tactics.V2.Derived.fst"
                                                              (Prims.of_int (376))
                                                              (Prims.of_int (20))
                                                              (Prims.of_int (376))
                                                              (Prims.of_int (28)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V2.Derived.fst"
                                                              (Prims.of_int (376))
                                                              (Prims.of_int (20))
                                                              (Prims.of_int (376))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (42)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (376))
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
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (376))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (376))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (375))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (378))
                                                               (Prims.of_int (28)))))
                                                      (Obj.magic uu___8)
                                                      (fun uu___9 ->
                                                         (fun uu___9 ->
                                                            match uu___9 with
                                                            | (gs', sgs') ->
                                                                let uu___10 =
                                                                  FStarC_Tactics_V2_Builtins.set_goals
                                                                    gs in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (378))
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
                                                                    (FStarC_Tactics_V2_Builtins.set_smt_goals
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
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (384)) (Prims.of_int (21))
                      (Prims.of_int (384)) (Prims.of_int (25)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (384)) (Prims.of_int (27))
                      (Prims.of_int (384)) (Prims.of_int (36)))))
             (Obj.magic uu___1)
             (fun uu___2 -> (fun uu___2 -> Obj.magic (iterAll g)) uu___2))
let (exact_args :
  FStarC_Reflection_V2_Data.aqualv Prims.list ->
    FStar_Tactics_NamedView.term ->
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
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (388)) (Prims.of_int (16))
                      (Prims.of_int (388)) (Prims.of_int (39)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (388)) (Prims.of_int (42))
                      (Prims.of_int (394)) (Prims.of_int (44)))))
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
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (389)) (Prims.of_int (18))
                                 (Prims.of_int (389)) (Prims.of_int (55)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (389)) (Prims.of_int (58))
                                 (Prims.of_int (394)) (Prims.of_int (44)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uvs ->
                              let uu___3 =
                                let uu___4 = FStar_Tactics_Util.zip uvs qs in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V2.Derived.fst"
                                           (Prims.of_int (390))
                                           (Prims.of_int (26))
                                           (Prims.of_int (390))
                                           (Prims.of_int (38)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V2.Derived.fst"
                                           (Prims.of_int (390))
                                           (Prims.of_int (17))
                                           (Prims.of_int (390))
                                           (Prims.of_int (38)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___6 ->
                                          FStar_Reflection_V2_Derived.mk_app
                                            t uu___5)) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (390))
                                            (Prims.of_int (17))
                                            (Prims.of_int (390))
                                            (Prims.of_int (38)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (391))
                                            (Prims.of_int (8))
                                            (Prims.of_int (394))
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
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (391))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (391))
                                                       (Prims.of_int (16)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Derived.fst"
                                                       (Prims.of_int (392))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (394))
                                                       (Prims.of_int (44)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun uu___5 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Util.iter
                                                         (fun uu___6 ->
                                                            (fun uv ->
                                                               if
                                                                 FStar_Reflection_V2_Derived.is_uvar
                                                                   uv
                                                               then
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStarC_Tactics_V2_Builtins.unshelve
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
    FStar_Tactics_NamedView.term ->
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
                     (fun uu___2 -> FStarC_Reflection_V2_Data.Q_Explicit)))
               uu___1) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (398)) (Prims.of_int (15))
                 (Prims.of_int (398)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (398)) (Prims.of_int (4)) (Prims.of_int (398))
                 (Prims.of_int (51))))) (Obj.magic uu___)
        (fun uu___1 -> (fun uu___1 -> Obj.magic (exact_args uu___1 t)) uu___1)
let (ngoals : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (401)) (Prims.of_int (47)) (Prims.of_int (401))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (401)) (Prims.of_int (26)) (Prims.of_int (401))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (404)) (Prims.of_int (51)) (Prims.of_int (404))
               (Prims.of_int (65)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (404)) (Prims.of_int (30)) (Prims.of_int (404))
               (Prims.of_int (65))))) (Obj.magic uu___1)
      (fun uu___2 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___3 -> FStar_List_Tot_Base.length uu___2))
let (fresh_namedv_named :
  Prims.string ->
    (FStar_Tactics_NamedView.namedv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (408)) (Prims.of_int (10)) (Prims.of_int (408))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (409)) (Prims.of_int (2)) (Prims.of_int (413))
               (Prims.of_int (4))))) (Obj.magic uu___)
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              FStar_Tactics_NamedView.pack_namedv
                {
                  FStarC_Reflection_V2_Data.uniq = n;
                  FStarC_Reflection_V2_Data.sort =
                    (FStar_Sealed.seal
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          FStarC_Reflection_V2_Data.Tv_Unknown));
                  FStarC_Reflection_V2_Data.ppname = (FStar_Sealed.seal s)
                }))
let (fresh_namedv :
  unit ->
    (FStar_Tactics_NamedView.namedv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (418)) (Prims.of_int (10)) (Prims.of_int (418))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (419)) (Prims.of_int (2)) (Prims.of_int (423))
               (Prims.of_int (4))))) (Obj.magic uu___1)
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              FStar_Tactics_NamedView.pack_namedv
                {
                  FStarC_Reflection_V2_Data.uniq = n;
                  FStarC_Reflection_V2_Data.sort =
                    (FStar_Sealed.seal
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          FStarC_Reflection_V2_Data.Tv_Unknown));
                  FStarC_Reflection_V2_Data.ppname =
                    (FStar_Sealed.seal
                       (Prims.strcat "x" (Prims.string_of_int n)))
                }))
let (fresh_binder_named :
  Prims.string ->
    FStarC_Reflection_Types.typ ->
      (FStar_Tactics_NamedView.simple_binder, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (426)) (Prims.of_int (10))
                 (Prims.of_int (426)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (428)) (Prims.of_int (4)) (Prims.of_int (432))
                 (Prims.of_int (17))))) (Obj.magic uu___)
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                {
                  FStar_Tactics_NamedView.uniq = n;
                  FStar_Tactics_NamedView.ppname = (FStar_Sealed.seal s);
                  FStar_Tactics_NamedView.sort = t;
                  FStar_Tactics_NamedView.qual =
                    FStarC_Reflection_V2_Data.Q_Explicit;
                  FStar_Tactics_NamedView.attrs = []
                }))
let (fresh_binder :
  FStarC_Reflection_Types.typ ->
    (FStar_Tactics_NamedView.simple_binder, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (436)) (Prims.of_int (10)) (Prims.of_int (436))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (438)) (Prims.of_int (4)) (Prims.of_int (442))
               (Prims.of_int (17))))) (Obj.magic uu___)
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              {
                FStar_Tactics_NamedView.uniq = n;
                FStar_Tactics_NamedView.ppname =
                  (FStar_Sealed.seal
                     (Prims.strcat "x" (Prims.string_of_int n)));
                FStar_Tactics_NamedView.sort = t;
                FStar_Tactics_NamedView.qual =
                  FStarC_Reflection_V2_Data.Q_Explicit;
                FStar_Tactics_NamedView.attrs = []
              }))
let (fresh_implicit_binder :
  FStarC_Reflection_Types.typ ->
    (FStar_Tactics_NamedView.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (446)) (Prims.of_int (10)) (Prims.of_int (446))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (448)) (Prims.of_int (4)) (Prims.of_int (452))
               (Prims.of_int (17))))) (Obj.magic uu___)
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              {
                FStar_Tactics_NamedView.uniq = n;
                FStar_Tactics_NamedView.ppname =
                  (FStar_Sealed.seal
                     (Prims.strcat "x" (Prims.string_of_int n)));
                FStar_Tactics_NamedView.sort = t;
                FStar_Tactics_NamedView.qual =
                  FStarC_Reflection_V2_Data.Q_Implicit;
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
      let uu___ = FStarC_Tactics_V2_Builtins.catch f in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (466)) (Prims.of_int (10))
                 (Prims.of_int (466)) (Prims.of_int (17)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (466)) (Prims.of_int (4)) (Prims.of_int (468))
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
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (471)) (Prims.of_int (13))
                        (Prims.of_int (471)) (Prims.of_int (19)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (471)) (Prims.of_int (8))
                        (Prims.of_int (471)) (Prims.of_int (19)))))
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
    let uu___ = FStarC_Tactics_V2_Builtins.catch t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (488)) (Prims.of_int (10)) (Prims.of_int (488))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (488)) (Prims.of_int (4)) (Prims.of_int (490))
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
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (490)) (Prims.of_int (20))
                                 (Prims.of_int (490)) (Prims.of_int (28)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (490)) (Prims.of_int (15))
                                 (Prims.of_int (490)) (Prims.of_int (28)))))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (493)) (Prims.of_int (4)) (Prims.of_int (493))
               (Prims.of_int (8)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (493)) (Prims.of_int (4)) (Prims.of_int (493))
               (Prims.of_int (20))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = repeat t in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (493)) (Prims.of_int (12))
                          (Prims.of_int (493)) (Prims.of_int (20)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (493)) (Prims.of_int (4))
                          (Prims.of_int (493)) (Prims.of_int (20)))))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (496)) (Prims.of_int (12)) (Prims.of_int (496))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (496)) (Prims.of_int (24)) (Prims.of_int (496))
               (Prims.of_int (26))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (norm_term :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      let uu___ =
        try_with (fun uu___1 -> match () with | () -> cur_env ())
          (fun uu___1 -> FStarC_Tactics_V2_Builtins.top_env ()) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (500)) (Prims.of_int (8)) (Prims.of_int (501))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (503)) (Prims.of_int (4)) (Prims.of_int (503))
                 (Prims.of_int (23))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              Obj.magic (FStarC_Tactics_V2_Builtins.norm_term_env e s t))
             uu___1)
let (join_all_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      let uu___2 = goals () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (510)) (Prims.of_int (16))
                 (Prims.of_int (510)) (Prims.of_int (24)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (510)) (Prims.of_int (16))
                 (Prims.of_int (510)) (Prims.of_int (38)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___4 = smt_goals () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (510)) (Prims.of_int (26))
                            (Prims.of_int (510)) (Prims.of_int (38)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (510)) (Prims.of_int (16))
                            (Prims.of_int (510)) (Prims.of_int (38)))))
                   (Obj.magic uu___4)
                   (fun uu___5 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___6 -> (uu___3, uu___5))))) uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (510)) (Prims.of_int (16)) (Prims.of_int (510))
               (Prims.of_int (38)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (509)) (Prims.of_int (27)) (Prims.of_int (516))
               (Prims.of_int (20))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | (gs, sgs) ->
                let uu___3 = FStarC_Tactics_V2_Builtins.set_smt_goals [] in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (511)) (Prims.of_int (2))
                              (Prims.of_int (511)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (512)) (Prims.of_int (2))
                              (Prims.of_int (516)) (Prims.of_int (20)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           let uu___5 =
                             FStarC_Tactics_V2_Builtins.set_goals sgs in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (512))
                                         (Prims.of_int (2))
                                         (Prims.of_int (512))
                                         (Prims.of_int (15)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Derived.fst"
                                         (Prims.of_int (513))
                                         (Prims.of_int (2))
                                         (Prims.of_int (516))
                                         (Prims.of_int (20)))))
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun uu___6 ->
                                      let uu___7 =
                                        repeat'
                                          FStarC_Tactics_V2_Builtins.join in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (513))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (513))
                                                    (Prims.of_int (14)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Derived.fst"
                                                    (Prims.of_int (513))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (516))
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
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (514))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (514))
                                                               (Prims.of_int (21)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Derived.fst"
                                                               (Prims.of_int (515))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (516))
                                                               (Prims.of_int (20)))))
                                                      (Obj.magic uu___9)
                                                      (fun uu___10 ->
                                                         (fun sgs' ->
                                                            let uu___10 =
                                                              FStarC_Tactics_V2_Builtins.set_goals
                                                                gs in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (14)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (20)))))
                                                                 (Obj.magic
                                                                    uu___10)
                                                                 (fun uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.set_smt_goals
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
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (519)) (Prims.of_int (22))
                 (Prims.of_int (519)) (Prims.of_int (28)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (519)) (Prims.of_int (32))
                 (Prims.of_int (519)) (Prims.of_int (34)))))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (523)) (Prims.of_int (12)) (Prims.of_int (523))
               (Prims.of_int (82)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (523)) (Prims.of_int (86)) (Prims.of_int (523))
               (Prims.of_int (88))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (tadmit : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V2_Builtins.tadmit_t
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (531)) (Prims.of_int (12)) (Prims.of_int (531))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (532)) (Prims.of_int (4)) (Prims.of_int (532))
               (Prims.of_int (6))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let (is_guard : unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = _cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (536)) (Prims.of_int (33)) (Prims.of_int (536))
               (Prims.of_int (47)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (536)) (Prims.of_int (4)) (Prims.of_int (536))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (539)) (Prims.of_int (7)) (Prims.of_int (539))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (539)) (Prims.of_int (4)) (Prims.of_int (541))
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (544)) (Prims.of_int (12)) (Prims.of_int (544))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (545)) (Prims.of_int (4)) (Prims.of_int (545))
               (Prims.of_int (6))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let (simpl : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V2_Builtins.norm
      [FStar_Pervasives.simplify; FStar_Pervasives.primops]
let (whnf : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V2_Builtins.norm
      [FStar_Pervasives.weak;
      FStar_Pervasives.hnf;
      FStar_Pervasives.primops;
      FStar_Pervasives.delta]
let (compute : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V2_Builtins.norm
      [FStar_Pervasives.primops;
      FStar_Pervasives.iota;
      FStar_Pervasives.delta;
      FStar_Pervasives.zeta]
let (intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStarC_Tactics_V2_Builtins.intros (Prims.of_int (-1))
let (intros' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = intros () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (553)) (Prims.of_int (36)) (Prims.of_int (553))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (553)) (Prims.of_int (49)) (Prims.of_int (553))
               (Prims.of_int (51))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let (destruct :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = FStarC_Tactics_V2_Builtins.t_destruct tm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (554)) (Prims.of_int (37)) (Prims.of_int (554))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (554)) (Prims.of_int (54)) (Prims.of_int (554))
               (Prims.of_int (56))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (destruct_intros :
  FStarC_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    seq
      (fun uu___ ->
         let uu___1 = FStarC_Tactics_V2_Builtins.t_destruct tm in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (555)) (Prims.of_int (59))
                    (Prims.of_int (555)) (Prims.of_int (72)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (555)) (Prims.of_int (76))
                    (Prims.of_int (555)) (Prims.of_int (78)))))
           (Obj.magic uu___1)
           (fun uu___2 ->
              FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))) intros'
let __cut : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
let (tcut :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (561)) (Prims.of_int (12)) (Prims.of_int (561))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (561)) (Prims.of_int (26)) (Prims.of_int (564))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun g ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_Reflection_V2_Derived.mk_e_app
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "V2";
                                 "Derived";
                                 "__cut"]))) [t; g])) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (562)) (Prims.of_int (13))
                          (Prims.of_int (562)) (Prims.of_int (37)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (563)) (Prims.of_int (4))
                          (Prims.of_int (564)) (Prims.of_int (12)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun tt ->
                       let uu___2 = apply tt in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (563)) (Prims.of_int (4))
                                     (Prims.of_int (563)) (Prims.of_int (12)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (564)) (Prims.of_int (4))
                                     (Prims.of_int (564)) (Prims.of_int (12)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  Obj.magic
                                    (FStarC_Tactics_V2_Builtins.intro ()))
                                 uu___3))) uu___2))) uu___1)
let (pose :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      apply
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "V2"; "Derived"; "__cut"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (567)) (Prims.of_int (4)) (Prims.of_int (567))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (568)) (Prims.of_int (4)) (Prims.of_int (570))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = flip () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (568)) (Prims.of_int (4))
                          (Prims.of_int (568)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (569)) (Prims.of_int (4))
                          (Prims.of_int (570)) (Prims.of_int (12)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 = exact t in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (569)) (Prims.of_int (4))
                                     (Prims.of_int (569)) (Prims.of_int (11)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (570)) (Prims.of_int (4))
                                     (Prims.of_int (570)) (Prims.of_int (12)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  Obj.magic
                                    (FStarC_Tactics_V2_Builtins.intro ()))
                                 uu___5))) uu___3))) uu___1)
let (intro_as :
  Prims.string ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    let uu___ = FStarC_Tactics_V2_Builtins.intro () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (573)) (Prims.of_int (12)) (Prims.of_int (573))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (574)) (Prims.of_int (4)) (Prims.of_int (574))
               (Prims.of_int (17))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b -> Obj.magic (FStarC_Tactics_V2_Builtins.rename_to b s))
           uu___1)
let (pose_as :
  Prims.string ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      let uu___ = pose t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (577)) (Prims.of_int (12))
                 (Prims.of_int (577)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (578)) (Prims.of_int (4)) (Prims.of_int (578))
                 (Prims.of_int (17))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun b -> Obj.magic (FStarC_Tactics_V2_Builtins.rename_to b s))
             uu___1)
let for_each_binding :
  'a .
    (FStar_Tactics_NamedView.binding ->
       ('a, unit) FStar_Tactics_Effect.tac_repr)
      -> ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    let uu___ = cur_vars () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (581)) (Prims.of_int (10)) (Prims.of_int (581))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (581)) (Prims.of_int (4)) (Prims.of_int (581))
               (Prims.of_int (23))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_Util.map f uu___1)) uu___1)
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
                (let uu___1 = FStarC_Tactics_V2_Builtins.revert () in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (586)) (Prims.of_int (15))
                            (Prims.of_int (586)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (587)) (Prims.of_int (13))
                            (Prims.of_int (587)) (Prims.of_int (26)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 -> Obj.magic (revert_all tl)) uu___2))))
      uu___
let (binder_sort :
  FStar_Tactics_NamedView.binder -> FStarC_Reflection_Types.typ) =
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
                               let uu___2 =
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
                                          "FStar.Tactics.V2.Derived.fst"
                                          (Prims.of_int (599))
                                          (Prims.of_int (13))
                                          (Prims.of_int (599))
                                          (Prims.of_int (48)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Derived.fst"
                                          (Prims.of_int (600))
                                          (Prims.of_int (13))
                                          (Prims.of_int (600))
                                          (Prims.of_int (20)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun uu___3 ->
                                       Obj.magic
                                         (exact
                                            (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                               b))) uu___3))
                        (fun uu___1 -> __assumption_aux bs))))) uu___
let (assumption : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = cur_vars () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (604)) (Prims.of_int (21)) (Prims.of_int (604))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (604)) (Prims.of_int (4)) (Prims.of_int (604))
               (Prims.of_int (34))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (__assumption_aux uu___2)) uu___2)
let (destruct_equality_implication :
  FStar_Tactics_NamedView.term ->
    ((FStar_Reflection_V2_Formula.formula * FStar_Tactics_NamedView.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Formula.term_as_formula t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (607)) (Prims.of_int (10)) (Prims.of_int (607))
               (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (607)) (Prims.of_int (4)) (Prims.of_int (614))
               (Prims.of_int (15))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V2_Formula.Implies (lhs, rhs) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        FStar_Reflection_V2_Formula.term_as_formula' lhs in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (609)) (Prims.of_int (18))
                                 (Prims.of_int (609)) (Prims.of_int (38)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (610)) (Prims.of_int (14))
                                 (Prims.of_int (612)) (Prims.of_int (19)))))
                        (Obj.magic uu___2)
                        (fun lhs1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                match lhs1 with
                                | FStar_Reflection_V2_Formula.Comp
                                    (FStar_Reflection_V2_Formula.Eq uu___4,
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
  FStar_Tactics_NamedView.binding ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    op_Less_Bar_Greater
      (op_Less_Bar_Greater
         (fun uu___ -> FStarC_Tactics_V2_Builtins.rewrite x)
         (fun uu___ ->
            let uu___1 = FStarC_Tactics_V2_Builtins.var_retype x in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                       (Prims.of_int (623)) (Prims.of_int (20))
                       (Prims.of_int (623)) (Prims.of_int (32)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                       (Prims.of_int (624)) (Prims.of_int (20))
                       (Prims.of_int (625)) (Prims.of_int (29)))))
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
                                 "V2";
                                 "Derived";
                                 "__eq_sym"]))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (624)) (Prims.of_int (20))
                                  (Prims.of_int (624)) (Prims.of_int (43)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (625)) (Prims.of_int (20))
                                  (Prims.of_int (625)) (Prims.of_int (29)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun uu___4 ->
                               Obj.magic
                                 (FStarC_Tactics_V2_Builtins.rewrite x))
                              uu___4))) uu___2)))
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
                    (let uu___ =
                       FStar_Reflection_V2_Formula.term_as_formula
                         (type_of_binding x_t) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (633)) (Prims.of_int (20))
                                (Prims.of_int (633)) (Prims.of_int (57)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (633)) (Prims.of_int (14))
                                (Prims.of_int (639)) (Prims.of_int (37)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | FStar_Reflection_V2_Formula.Comp
                                 (FStar_Reflection_V2_Formula.Eq uu___2, y,
                                  uu___3)
                                 ->
                                 if term_eq x y
                                 then
                                   Obj.magic
                                     (FStarC_Tactics_V2_Builtins.rewrite x_t)
                                 else Obj.magic (try_rewrite_equality x bs1)
                             | uu___2 ->
                                 Obj.magic (try_rewrite_equality x bs1))
                            uu___1)))) uu___1 uu___
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
                (let uu___ =
                   try_with
                     (fun uu___1 ->
                        match () with
                        | () -> FStarC_Tactics_V2_Builtins.rewrite x_t)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> ()))) uu___1) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (646)) (Prims.of_int (8))
                            (Prims.of_int (646)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (647)) (Prims.of_int (8))
                            (Prims.of_int (647)) (Prims.of_int (41)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic (rewrite_all_context_equalities bs1))
                        uu___1)))) uu___
let (rewrite_eqs_from_context :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = cur_vars () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (651)) (Prims.of_int (35)) (Prims.of_int (651))
               (Prims.of_int (48)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (651)) (Prims.of_int (4)) (Prims.of_int (651))
               (Prims.of_int (48))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (rewrite_all_context_equalities uu___2))
           uu___2)
let (rewrite_equality :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = cur_vars () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (654)) (Prims.of_int (27)) (Prims.of_int (654))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (654)) (Prims.of_int (4)) (Prims.of_int (654))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (try_rewrite_equality t uu___1)) uu___1)
let (unfold_def :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (657)) (Prims.of_int (10)) (Prims.of_int (657))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (657)) (Prims.of_int (4)) (Prims.of_int (661))
               (Prims.of_int (46))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                FStarC_Reflection_V2_Builtins.implode_qn
                                  (FStarC_Reflection_V2_Builtins.inspect_fv
                                     fv))) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (659)) (Prims.of_int (16))
                                 (Prims.of_int (659)) (Prims.of_int (42)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (660)) (Prims.of_int (8))
                                 (Prims.of_int (660)) (Prims.of_int (30)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun n ->
                              Obj.magic
                                (FStarC_Tactics_V2_Builtins.norm
                                   [FStar_Pervasives.delta_fully [n]]))
                             uu___3)))
            | uu___2 ->
                Obj.magic (Obj.repr (fail "unfold_def: term is not a fv")))
           uu___1)
let (l_to_r :
  FStar_Tactics_NamedView.term Prims.list ->
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
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (668)) (Prims.of_int (8))
                           (Prims.of_int (671)) (Prims.of_int (31)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                           (Prims.of_int (668)) (Prims.of_int (8))
                           (Prims.of_int (671)) (Prims.of_int (31)))))
                  (Obj.magic uu___3)
                  (fun uu___4 -> (fun uu___4 -> Obj.magic (uu___4 ())) uu___4))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (668)) (Prims.of_int (8)) (Prims.of_int (671))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (672)) (Prims.of_int (4)) (Prims.of_int (672))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun first_or_trefl -> Obj.magic (pointwise first_or_trefl)) uu___1)
let (mk_squash :
  FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term) =
  fun t ->
    let sq =
      FStar_Tactics_NamedView.pack
        (FStar_Tactics_NamedView.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
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
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) in
      mk_squash (FStar_Reflection_V2_Derived.mk_e_app eq [t1; t2])
let (__grewrite_derived :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = tcut (mk_sq_eq t1 t2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (687)) (Prims.of_int (12))
                 (Prims.of_int (687)) (Prims.of_int (33)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (687)) (Prims.of_int (36))
                 (Prims.of_int (703)) (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_Tactics_NamedView.pack
                          (FStar_Tactics_NamedView.Tv_Var
                             (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                e)))) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (688)) (Prims.of_int (12))
                            (Prims.of_int (688)) (Prims.of_int (27)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (689)) (Prims.of_int (4))
                            (Prims.of_int (703)) (Prims.of_int (5)))))
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
                                                "FStar.Tactics.V2.Derived.fst"
                                                (Prims.of_int (691))
                                                (Prims.of_int (30))
                                                (Prims.of_int (691))
                                                (Prims.of_int (42)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Derived.fst"
                                                (Prims.of_int (691))
                                                (Prims.of_int (14))
                                                (Prims.of_int (691))
                                                (Prims.of_int (42)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             Obj.magic
                                               (FStar_Reflection_V2_Formula.term_as_formula
                                                  uu___6)) uu___6) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.V2.Derived.fst"
                                              (Prims.of_int (691))
                                              (Prims.of_int (14))
                                              (Prims.of_int (691))
                                              (Prims.of_int (42)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.V2.Derived.fst"
                                              (Prims.of_int (691))
                                              (Prims.of_int (8))
                                              (Prims.of_int (695))
                                              (Prims.of_int (20)))))
                                     (Obj.magic uu___4)
                                     (fun uu___5 ->
                                        match uu___5 with
                                        | FStar_Reflection_V2_Formula.Comp
                                            (FStar_Reflection_V2_Formula.Eq
                                             uu___6, lhs, rhs)
                                            ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 -> (lhs, rhs))
                                        | uu___6 ->
                                            FStar_Tactics_Effect.raise
                                              FStarC_Tactics_Common.SKIP) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (691))
                                            (Prims.of_int (8))
                                            (Prims.of_int (695))
                                            (Prims.of_int (20)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Derived.fst"
                                            (Prims.of_int (689))
                                            (Prims.of_int (24))
                                            (Prims.of_int (702))
                                            (Prims.of_int (40)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         match uu___4 with
                                         | (lhs, rhs) ->
                                             let uu___5 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 -> uu___4)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.V2.Derived.fst"
                                                           (Prims.of_int (697))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (702))
                                                           (Prims.of_int (40)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.V2.Derived.fst"
                                                           (Prims.of_int (697))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (702))
                                                           (Prims.of_int (40)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun uu___6 ->
                                                        let uu___7 =
                                                          let uu___8 =
                                                            FStar_Tactics_NamedView.inspect
                                                              lhs in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (14)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (21)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___10
                                                                    ->
                                                                    FStar_Tactics_NamedView.uu___is_Tv_Uvar
                                                                    uu___9)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (21)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (40)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                (fun uu___8
                                                                   ->
                                                                   if uu___8
                                                                   then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (trefl ()))
                                                                   else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (term_eq
                                                                    lhs t1)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    FStarC_Tactics_Common.SKIP)
                                                                    else
                                                                    Obj.repr
                                                                    (try_with
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    exact e1)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    trefl ())))))
                                                                  uu___8)))
                                                       uu___6))) uu___4))))
                        uu___2))) uu___1)
let (grewrite_eq :
  FStar_Tactics_NamedView.binding ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      FStar_Reflection_V2_Formula.term_as_formula (type_of_binding b) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (710)) (Prims.of_int (8)) (Prims.of_int (710))
               (Prims.of_int (43)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (710)) (Prims.of_int (2)) (Prims.of_int (722))
               (Prims.of_int (7))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V2_Formula.Comp
                (FStar_Reflection_V2_Formula.Eq uu___2, l, r) ->
                let uu___3 = FStarC_Tactics_V2_Builtins.grewrite l r in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (712)) (Prims.of_int (4))
                              (Prims.of_int (712)) (Prims.of_int (16)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (713)) (Prims.of_int (4))
                              (Prims.of_int (713)) (Prims.of_int (37)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           Obj.magic
                             (iseq
                                [idtac;
                                (fun uu___5 ->
                                   exact
                                     (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                        b))])) uu___4))
            | uu___2 ->
                let uu___3 =
                  FStar_Reflection_V2_Formula.term_as_formula'
                    (type_of_binding b) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (715)) (Prims.of_int (16))
                              (Prims.of_int (715)) (Prims.of_int (52)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (715)) (Prims.of_int (10))
                              (Prims.of_int (721)) (Prims.of_int (56)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 ->
                           match uu___4 with
                           | FStar_Reflection_V2_Formula.Comp
                               (FStar_Reflection_V2_Formula.Eq uu___5, l, r)
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___6 =
                                       FStarC_Tactics_V2_Builtins.grewrite l
                                         r in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Derived.fst"
                                                (Prims.of_int (717))
                                                (Prims.of_int (6))
                                                (Prims.of_int (717))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Derived.fst"
                                                (Prims.of_int (718))
                                                (Prims.of_int (6))
                                                (Prims.of_int (719))
                                                (Prims.of_int (39)))))
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
                                                                  "V2";
                                                                  "Derived";
                                                                  "__un_sq_eq"]))) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Derived.fst"
                                                                (Prims.of_int (718))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (718))
                                                                (Prims.of_int (55)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Derived.fst"
                                                                (Prims.of_int (719))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (719))
                                                                (Prims.of_int (37)))))
                                                       (Obj.magic uu___9)
                                                       (fun uu___10 ->
                                                          (fun uu___10 ->
                                                             Obj.magic
                                                               (exact
                                                                  (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b)))
                                                            uu___10))]))
                                            uu___7)))
                           | uu___5 ->
                               Obj.magic
                                 (Obj.repr
                                    (fail
                                       "grewrite_eq: binder type is not an equality")))
                          uu___4))) uu___1)
let (admit_dump_t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.dump "Admitting" in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (726)) (Prims.of_int (2)) (Prims.of_int (726))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (727)) (Prims.of_int (2)) (Prims.of_int (727))
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
    let uu___1 = FStarC_Tactics_V2_Builtins.dump "Admitting" in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (734)) (Prims.of_int (2)) (Prims.of_int (734))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (735)) (Prims.of_int (2)) (Prims.of_int (737))
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
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (735)) (Prims.of_int (2))
                          (Prims.of_int (735)) (Prims.of_int (16)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (736)) (Prims.of_int (2))
                          (Prims.of_int (737)) (Prims.of_int (4)))))
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
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (736)) (Prims.of_int (2))
                                     (Prims.of_int (736)) (Prims.of_int (13)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (737)) (Prims.of_int (2))
                                     (Prims.of_int (737)) (Prims.of_int (4)))))
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
           let uu___1 = FStarC_Tactics_V2_Builtins.grewrite t1 t2 in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (744)) (Prims.of_int (8))
                      (Prims.of_int (744)) (Prims.of_int (22)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                      (Prims.of_int (745)) (Prims.of_int (8))
                      (Prims.of_int (745)) (Prims.of_int (29)))))
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun uu___2 -> Obj.magic (iseq [idtac; trivial])) uu___2))
let (change_sq :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    FStarC_Tactics_V2_Builtins.change
      (FStar_Reflection_V2_Derived.mk_e_app
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
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (752)) (Prims.of_int (12)) (Prims.of_int (752))
               (Prims.of_int (16)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (753)) (Prims.of_int (4)) (Prims.of_int (754))
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
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (753)) (Prims.of_int (4))
                          (Prims.of_int (753)) (Prims.of_int (58)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (752)) (Prims.of_int (8))
                          (Prims.of_int (752)) (Prims.of_int (9)))))
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
      let uu___ = FStarC_Tactics_V2_Builtins.dup () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (757)) (Prims.of_int (4)) (Prims.of_int (757))
                 (Prims.of_int (10)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (757)) (Prims.of_int (11))
                 (Prims.of_int (761)) (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 = focus (fun uu___3 -> finish_by t1) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (758)) (Prims.of_int (12))
                            (Prims.of_int (758)) (Prims.of_int (42)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (758)) (Prims.of_int (45))
                            (Prims.of_int (761)) (Prims.of_int (5)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun x ->
                         let uu___3 = t2 x in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (759))
                                       (Prims.of_int (12))
                                       (Prims.of_int (759))
                                       (Prims.of_int (16)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.V2.Derived.fst"
                                       (Prims.of_int (760))
                                       (Prims.of_int (4))
                                       (Prims.of_int (761))
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
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (760))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (760))
                                                  (Prims.of_int (12)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.V2.Derived.fst"
                                                  (Prims.of_int (759))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (759))
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
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (764)) (Prims.of_int (4))
                    (Prims.of_int (764)) (Prims.of_int (17)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (765)) (Prims.of_int (4))
                    (Prims.of_int (769)) (Prims.of_int (5)))))
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
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (766)) (Prims.of_int (14))
                                    (Prims.of_int (766)) (Prims.of_int (18)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Derived.fst"
                                    (Prims.of_int (767)) (Prims.of_int (6))
                                    (Prims.of_int (768)) (Prims.of_int (7)))))
                           (Obj.magic uu___4)
                           (fun uu___5 ->
                              (fun x ->
                                 let uu___5 = qed () in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (767))
                                               (Prims.of_int (6))
                                               (Prims.of_int (767))
                                               (Prims.of_int (12)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (766))
                                               (Prims.of_int (10))
                                               (Prims.of_int (766))
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
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (788)) (Prims.of_int (42))
                        (Prims.of_int (788)) (Prims.of_int (51)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                        (Prims.of_int (788)) (Prims.of_int (36))
                        (Prims.of_int (788)) (Prims.of_int (51)))))
               (Obj.magic uu___2)
               (fun uu___3 -> (fun uu___3 -> Obj.magic (exact uu___3)) uu___3))
          (fun uu___1 ->
             FStarC_Tactics_V2_Builtins.norm
               [FStar_Pervasives.delta_only l;
               FStar_Pervasives.iota;
               FStar_Pervasives.zeta])
let (tlabel : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (791)) (Prims.of_int (10)) (Prims.of_int (791))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (791)) (Prims.of_int (4)) (Prims.of_int (794))
               (Prims.of_int (38))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | [] -> Obj.magic (Obj.repr (fail "tlabel: no goals"))
            | h::t ->
                Obj.magic
                  (Obj.repr
                     (FStarC_Tactics_V2_Builtins.set_goals
                        ((FStarC_Tactics_Types.set_label l h) :: t)))) uu___1)
let (tlabel' : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    let uu___ = goals () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (797)) (Prims.of_int (10)) (Prims.of_int (797))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (797)) (Prims.of_int (4)) (Prims.of_int (801))
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
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (800)) (Prims.of_int (16))
                                 (Prims.of_int (800)) (Prims.of_int (45)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (801)) (Prims.of_int (8))
                                 (Prims.of_int (801)) (Prims.of_int (26)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun h1 ->
                              Obj.magic
                                (FStarC_Tactics_V2_Builtins.set_goals (h1 ::
                                   t))) uu___3)))) uu___1)
let (focus_all : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        let uu___3 = goals () in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (804)) (Prims.of_int (15))
                   (Prims.of_int (804)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (804)) (Prims.of_int (14))
                   (Prims.of_int (804)) (Prims.of_int (39)))))
          (Obj.magic uu___3)
          (fun uu___4 ->
             (fun uu___4 ->
                let uu___5 = smt_goals () in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (804)) (Prims.of_int (26))
                              (Prims.of_int (804)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (804)) (Prims.of_int (14))
                              (Prims.of_int (804)) (Prims.of_int (39)))))
                     (Obj.magic uu___5)
                     (fun uu___6 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___7 -> (op_At ()) uu___4 uu___6)))) uu___4) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (804)) (Prims.of_int (14))
                 (Prims.of_int (804)) (Prims.of_int (39)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (804)) (Prims.of_int (4)) (Prims.of_int (804))
                 (Prims.of_int (39))))) (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              Obj.magic (FStarC_Tactics_V2_Builtins.set_goals uu___3)) uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (804)) (Prims.of_int (4)) (Prims.of_int (804))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (805)) (Prims.of_int (4)) (Prims.of_int (805))
               (Prims.of_int (20))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            Obj.magic (FStarC_Tactics_V2_Builtins.set_smt_goals [])) uu___2)
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
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (820)) (Prims.of_int (28))
                 (Prims.of_int (820)) (Prims.of_int (38)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (820)) (Prims.of_int (8)) (Prims.of_int (820))
                 (Prims.of_int (38))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> extract_nth (n - Prims.int_one) uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (820)) (Prims.of_int (8)) (Prims.of_int (820))
               (Prims.of_int (38)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (820)) (Prims.of_int (2)) (Prims.of_int (822))
               (Prims.of_int (37))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                Obj.magic (Obj.repr (fail "bump_nth: not that many goals"))
            | FStar_Pervasives_Native.Some (h, t) ->
                Obj.magic
                  (Obj.repr (FStarC_Tactics_V2_Builtins.set_goals (h :: t))))
           uu___1)
let rec (destruct_list :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_V2_SyntaxHelpers.collect_app t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (825)) (Prims.of_int (21)) (Prims.of_int (825))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (824)) (Prims.of_int (52)) (Prims.of_int (837))
               (Prims.of_int (27))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (head, args) ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_NamedView.inspect head in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (826)) (Prims.of_int (10))
                             (Prims.of_int (826)) (Prims.of_int (22)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.V2.Derived.fst"
                             (Prims.of_int (826)) (Prims.of_int (10))
                             (Prims.of_int (826)) (Prims.of_int (28)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 -> (uu___4, args))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (826)) (Prims.of_int (10))
                              (Prims.of_int (826)) (Prims.of_int (28)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.Derived.fst"
                              (Prims.of_int (826)) (Prims.of_int (4))
                              (Prims.of_int (837)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | (FStar_Tactics_NamedView.Tv_FVar fv,
                              (a1, FStarC_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStarC_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.cons_qn
                                     then
                                       Obj.repr
                                         (let uu___4 = destruct_list a2 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 -> a1 :: uu___5)))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_Effect.raise
                                            FStarC_Tactics_Common.NotAListLiteral)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv,
                              (uu___4, FStarC_Reflection_V2_Data.Q_Implicit)::
                              (a1, FStarC_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStarC_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.cons_qn
                                     then
                                       Obj.repr
                                         (let uu___5 = destruct_list a2 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Derived.fst"
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (830))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 -> a1 :: uu___6)))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_Effect.raise
                                            FStarC_Tactics_Common.NotAListLiteral)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv, uu___4) ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStarC_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.nil_qn
                                     then
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 -> [])
                                     else
                                       FStar_Tactics_Effect.raise
                                         FStarC_Tactics_Common.NotAListLiteral))
                           | uu___4 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.raise
                                       FStarC_Tactics_Common.NotAListLiteral)))
                          uu___3))) uu___1)
let (get_match_body :
  unit -> (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      let uu___2 = cur_goal () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (840)) (Prims.of_int (22))
                 (Prims.of_int (840)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (840)) (Prims.of_int (8)) (Prims.of_int (840))
                 (Prims.of_int (35))))) (Obj.magic uu___2)
        (fun uu___3 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___4 -> FStar_Reflection_V2_Derived.unsquash_term uu___3)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (840)) (Prims.of_int (8)) (Prims.of_int (840))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (840)) (Prims.of_int (2)) (Prims.of_int (844))
               (Prims.of_int (46))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            match uu___2 with
            | FStar_Pervasives_Native.None -> Obj.magic (Obj.repr (fail ""))
            | FStar_Pervasives_Native.Some t ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        FStar_Tactics_V2_SyntaxHelpers.inspect_unascribe t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (842)) (Prims.of_int (20))
                                 (Prims.of_int (842)) (Prims.of_int (39)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.V2.Derived.fst"
                                 (Prims.of_int (842)) (Prims.of_int (14))
                                 (Prims.of_int (844)) (Prims.of_int (46)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           match uu___4 with
                           | FStar_Tactics_NamedView.Tv_Match
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
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (857)) (Prims.of_int (14))
                    (Prims.of_int (857)) (Prims.of_int (31)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                    (Prims.of_int (857)) (Prims.of_int (34))
                    (Prims.of_int (863)) (Prims.of_int (20)))))
           (Obj.magic uu___2)
           (fun uu___3 ->
              (fun x ->
                 let uu___3 = FStarC_Tactics_V2_Builtins.t_destruct x in
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Derived.fst"
                               (Prims.of_int (858)) (Prims.of_int (14))
                               (Prims.of_int (858)) (Prims.of_int (26)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Derived.fst"
                               (Prims.of_int (859)) (Prims.of_int (6))
                               (Prims.of_int (863)) (Prims.of_int (20)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            Obj.magic
                              (iterAll
                                 (fun uu___5 ->
                                    let uu___6 =
                                      repeat FStarC_Tactics_V2_Builtins.intro in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (860))
                                               (Prims.of_int (17))
                                               (Prims.of_int (860))
                                               (Prims.of_int (29)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.V2.Derived.fst"
                                               (Prims.of_int (860))
                                               (Prims.of_int (32))
                                               (Prims.of_int (863))
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
                                                          "FStar.Tactics.V2.Derived.fst"
                                                          (Prims.of_int (861))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (861))
                                                          (Prims.of_int (23)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.V2.Derived.fst"
                                                          (Prims.of_int (862))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (863))
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
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (862))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (862))
                                                                    (Prims.of_int (21)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Derived.fst"
                                                                    (Prims.of_int (863))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (863))
                                                                    (Prims.of_int (19)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               (fun uu___9 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Tactics_V2_Builtins.norm
                                                                    [FStar_Pervasives.iota]))
                                                                 uu___9)))
                                                      uu___8))) uu___7))))
                           uu___4))) uu___3))
let (nth_var :
  Prims.int ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun i ->
    let uu___ = cur_vars () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (872)) (Prims.of_int (11)) (Prims.of_int (872))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (872)) (Prims.of_int (25)) (Prims.of_int (877))
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
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (873)) (Prims.of_int (16))
                          (Prims.of_int (873)) (Prims.of_int (65)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (873)) (Prims.of_int (68))
                          (Prims.of_int (877)) (Prims.of_int (15)))))
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
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (874)) (Prims.of_int (16))
                                     (Prims.of_int (874)) (Prims.of_int (62)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Derived.fst"
                                     (Prims.of_int (875)) (Prims.of_int (2))
                                     (Prims.of_int (877)) (Prims.of_int (15)))))
                            (Obj.magic uu___2)
                            (fun k1 ->
                               match FStar_List_Tot_Base.nth bs k1 with
                               | FStar_Pervasives_Native.None ->
                                   fail "not enough binders"
                               | FStar_Pervasives_Native.Some b ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> b)))) uu___2))) uu___1)
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
                    (let uu___ = mk_abs args' t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (884)) (Prims.of_int (13))
                                (Prims.of_int (884)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic uu___)
                       (fun t' ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Tactics_NamedView.pack
                                 (FStar_Tactics_NamedView.Tv_Abs (a, t')))))))
        uu___1 uu___
let (namedv_to_simple_binder :
  FStar_Tactics_NamedView.namedv ->
    (FStar_Tactics_NamedView.simple_binder, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun n ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Tactics_NamedView.inspect_namedv n)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (889)) (Prims.of_int (11)) (Prims.of_int (889))
               (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (891)) (Prims.of_int (4)) (Prims.of_int (895))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun nv ->
            let uu___1 =
              FStarC_Tactics_Unseal.unseal nv.FStarC_Reflection_V2_Data.sort in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (893)) (Prims.of_int (13))
                          (Prims.of_int (893)) (Prims.of_int (27)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                          (Prims.of_int (891)) (Prims.of_int (4))
                          (Prims.of_int (895)) (Prims.of_int (16)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 ->
                         {
                           FStar_Tactics_NamedView.uniq =
                             (nv.FStarC_Reflection_V2_Data.uniq);
                           FStar_Tactics_NamedView.ppname =
                             (nv.FStarC_Reflection_V2_Data.ppname);
                           FStar_Tactics_NamedView.sort = uu___2;
                           FStar_Tactics_NamedView.qual =
                             FStarC_Reflection_V2_Data.Q_Explicit;
                           FStar_Tactics_NamedView.attrs = []
                         })))) uu___1)
let (binding_to_simple_binder :
  FStar_Tactics_NamedView.binding -> FStar_Tactics_NamedView.simple_binder) =
  fun b ->
    {
      FStar_Tactics_NamedView.uniq = (b.FStarC_Reflection_V2_Data.uniq1);
      FStar_Tactics_NamedView.ppname = (b.FStarC_Reflection_V2_Data.ppname3);
      FStar_Tactics_NamedView.sort = (b.FStarC_Reflection_V2_Data.sort3);
      FStar_Tactics_NamedView.qual = FStarC_Reflection_V2_Data.Q_Explicit;
      FStar_Tactics_NamedView.attrs = []
    }
let (string_to_term_with_lb :
  (Prims.string * FStar_Tactics_NamedView.term) Prims.list ->
    FStarC_Reflection_Types.env ->
      Prims.string ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun letbindings ->
    fun e ->
      fun t ->
        let uu___ =
          FStar_Tactics_Util.fold_left
            (fun uu___1 ->
               fun uu___2 ->
                 match (uu___1, uu___2) with
                 | ((e1, lb_bvs), (i, v)) ->
                     let uu___3 =
                       FStarC_Tactics_V2_Builtins.push_bv_dsenv e1 i in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (916)) (Prims.of_int (19))
                                (Prims.of_int (916)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Derived.fst"
                                (Prims.of_int (915)) (Prims.of_int (42))
                                (Prims.of_int (917)) (Prims.of_int (25)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 ->
                               match uu___4 with
                               | (e2, b) -> (e2, ((v, b) :: lb_bvs)))))
            (e, []) letbindings in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (915)) (Prims.of_int (6))
                   (Prims.of_int (918)) (Prims.of_int (27)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                   (Prims.of_int (914)) (Prims.of_int (3))
                   (Prims.of_int (922)) (Prims.of_int (21)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (e1, lb_bindings) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 -> uu___1)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (918)) (Prims.of_int (30))
                                  (Prims.of_int (922)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.Derived.fst"
                                  (Prims.of_int (918)) (Prims.of_int (30))
                                  (Prims.of_int (922)) (Prims.of_int (21)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___4 =
                                 FStarC_Tactics_V2_Builtins.string_to_term e1
                                   t in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (919))
                                             (Prims.of_int (12))
                                             (Prims.of_int (919))
                                             (Prims.of_int (30)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.V2.Derived.fst"
                                             (Prims.of_int (920))
                                             (Prims.of_int (4))
                                             (Prims.of_int (922))
                                             (Prims.of_int (21)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun t1 ->
                                          Obj.magic
                                            (FStar_Tactics_Util.fold_left
                                               (fun uu___6 ->
                                                  fun uu___5 ->
                                                    (fun t2 ->
                                                       fun uu___5 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___6 ->
                                                                 match uu___5
                                                                 with
                                                                 | (i, b) ->
                                                                    FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Let
                                                                    (false,
                                                                    [],
                                                                    (binding_to_simple_binder
                                                                    b), i,
                                                                    t2)))))
                                                      uu___6 uu___5) t1
                                               lb_bindings)) uu___5))) uu___3)))
               uu___1)
let (trans : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V2"; "Derived"; "lem_trans"])))
let (smt_sync : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.get_vconfig () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (934)) (Prims.of_int (40)) (Prims.of_int (934))
               (Prims.of_int (56)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
               (Prims.of_int (934)) (Prims.of_int (29)) (Prims.of_int (934))
               (Prims.of_int (56))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            Obj.magic (FStarC_Tactics_V2_Builtins.t_smt_sync uu___2)) uu___2)
let (smt_sync' :
  Prims.nat -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun fuel ->
    fun ifuel ->
      let uu___ = FStarC_Tactics_V2_Builtins.get_vconfig () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (938)) (Prims.of_int (15))
                 (Prims.of_int (938)) (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                 (Prims.of_int (938)) (Prims.of_int (32))
                 (Prims.of_int (942)) (Prims.of_int (20)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun vcfg ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        {
                          FStarC_VConfig.initial_fuel = fuel;
                          FStarC_VConfig.max_fuel = fuel;
                          FStarC_VConfig.initial_ifuel = ifuel;
                          FStarC_VConfig.max_ifuel = ifuel;
                          FStarC_VConfig.detail_errors =
                            (vcfg.FStarC_VConfig.detail_errors);
                          FStarC_VConfig.detail_hint_replay =
                            (vcfg.FStarC_VConfig.detail_hint_replay);
                          FStarC_VConfig.no_smt =
                            (vcfg.FStarC_VConfig.no_smt);
                          FStarC_VConfig.quake_lo =
                            (vcfg.FStarC_VConfig.quake_lo);
                          FStarC_VConfig.quake_hi =
                            (vcfg.FStarC_VConfig.quake_hi);
                          FStarC_VConfig.quake_keep =
                            (vcfg.FStarC_VConfig.quake_keep);
                          FStarC_VConfig.retry = (vcfg.FStarC_VConfig.retry);
                          FStarC_VConfig.smtencoding_elim_box =
                            (vcfg.FStarC_VConfig.smtencoding_elim_box);
                          FStarC_VConfig.smtencoding_nl_arith_repr =
                            (vcfg.FStarC_VConfig.smtencoding_nl_arith_repr);
                          FStarC_VConfig.smtencoding_l_arith_repr =
                            (vcfg.FStarC_VConfig.smtencoding_l_arith_repr);
                          FStarC_VConfig.smtencoding_valid_intro =
                            (vcfg.FStarC_VConfig.smtencoding_valid_intro);
                          FStarC_VConfig.smtencoding_valid_elim =
                            (vcfg.FStarC_VConfig.smtencoding_valid_elim);
                          FStarC_VConfig.tcnorm =
                            (vcfg.FStarC_VConfig.tcnorm);
                          FStarC_VConfig.no_plugins =
                            (vcfg.FStarC_VConfig.no_plugins);
                          FStarC_VConfig.no_tactics =
                            (vcfg.FStarC_VConfig.no_tactics);
                          FStarC_VConfig.z3cliopt =
                            (vcfg.FStarC_VConfig.z3cliopt);
                          FStarC_VConfig.z3smtopt =
                            (vcfg.FStarC_VConfig.z3smtopt);
                          FStarC_VConfig.z3refresh =
                            (vcfg.FStarC_VConfig.z3refresh);
                          FStarC_VConfig.z3rlimit =
                            (vcfg.FStarC_VConfig.z3rlimit);
                          FStarC_VConfig.z3rlimit_factor =
                            (vcfg.FStarC_VConfig.z3rlimit_factor);
                          FStarC_VConfig.z3seed =
                            (vcfg.FStarC_VConfig.z3seed);
                          FStarC_VConfig.z3version =
                            (vcfg.FStarC_VConfig.z3version);
                          FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns
                            =
                            (vcfg.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
                          FStarC_VConfig.reuse_hint_for =
                            (vcfg.FStarC_VConfig.reuse_hint_for)
                        })) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (939)) (Prims.of_int (18))
                            (Prims.of_int (940)) (Prims.of_int (68)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Derived.fst"
                            (Prims.of_int (942)) (Prims.of_int (4))
                            (Prims.of_int (942)) (Prims.of_int (20)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun vcfg' ->
                         Obj.magic
                           (FStarC_Tactics_V2_Builtins.t_smt_sync vcfg'))
                        uu___2))) uu___1)
let (check_equiv :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.typ ->
      FStarC_Reflection_Types.typ ->
        (((unit, unit, unit) FStarC_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun t1 -> FStarC_Tactics_V2_Builtins.t_check_equiv true true g t0 t1
let (check_equiv_nosmt :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.typ ->
      FStarC_Reflection_Types.typ ->
        (((unit, unit, unit) FStarC_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun t1 -> FStarC_Tactics_V2_Builtins.t_check_equiv false false g t0 t1