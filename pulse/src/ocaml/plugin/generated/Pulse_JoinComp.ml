open Prims
let (compute_iname_join :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun is1 -> fun is2 -> Pulse_Typing.tm_join_inames is1 is2
let (lift_atomic_to_st :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (Pulse_Syntax_Base.comp_st,
            (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  =
  fun g ->
    fun e ->
      fun c ->
        fun d ->
          let uu___ = c in
          match uu___ with
          | Pulse_Syntax_Base.C_STAtomic (uu___1, uu___2, c_st) ->
              let c' = Pulse_Syntax_Base.C_ST c_st in
              let d' =
                Pulse_Typing.T_Lift
                  (g, e, c, c', d, (Pulse_Typing.Lift_STAtomic_ST (g, c))) in
              Prims.Mkdtuple2 (c', d')
let (lift_ghost_to_atomic :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((Pulse_Syntax_Base.comp_st,
             (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun c ->
        fun d ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.JoinComp.fst"
                     (Prims.of_int (65)) (Prims.of_int (30))
                     (Prims.of_int (65)) (Prims.of_int (31)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.JoinComp.fst"
                     (Prims.of_int (65)) Prims.int_one (Prims.of_int (82))
                     (Prims.of_int (14)))))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> c))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | Pulse_Syntax_Base.C_STGhost (inames, c_st) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.JoinComp.fst"
                                    (Prims.of_int (67)) (Prims.of_int (26))
                                    (Prims.of_int (71)) (Prims.of_int (5)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.JoinComp.fst"
                                    (Prims.of_int (72)) (Prims.of_int (4))
                                    (Prims.of_int (82)) (Prims.of_int (14)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> ()))
                           (fun uu___1 ->
                              (fun comp_res_typing ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.JoinComp.fst"
                                               (Prims.of_int (73))
                                               (Prims.of_int (34))
                                               (Prims.of_int (73))
                                               (Prims.of_int (103)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.JoinComp.fst"
                                               (Prims.of_int (74))
                                               (Prims.of_int (2))
                                               (Prims.of_int (82))
                                               (Prims.of_int (14)))))
                                      (Obj.magic
                                         (Pulse_Checker_Pure.get_non_informative_witness
                                            g (Pulse_Syntax_Base.comp_u c)
                                            (Pulse_Syntax_Base.comp_res c) ()))
                                      (fun uu___1 ->
                                         (fun w ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.JoinComp.fst"
                                                          (Prims.of_int (74))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (74))
                                                          (Prims.of_int (34)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.JoinComp.fst"
                                                          (Prims.of_int (82))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (82))
                                                          (Prims.of_int (14)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_BreakVC.break_vc
                                                       ()))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         Prims.Mkdtuple2
                                                           ((Pulse_Syntax_Base.C_STAtomic
                                                               (inames,
                                                                 Pulse_Syntax_Base.Neutral,
                                                                 c_st)),
                                                             (Pulse_Typing.T_Lift
                                                                (g, e, c,
                                                                  (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    Pulse_Syntax_Base.Neutral,
                                                                    c_st)),
                                                                  d,
                                                                  (Pulse_Typing.Lift_Ghost_Neutral
                                                                    (g, c, w)))))))))
                                           uu___1))) uu___1))) uu___)
let (join_comps :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp_st ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  Pulse_Typing.post_hint_t ->
                    ((Pulse_Syntax_Base.comp_st,
                       (unit, unit, unit) Pulse_Typing.st_typing,
                       (unit, unit, unit) Pulse_Typing.st_typing)
                       FStar_Pervasives.dtuple3,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___8 ->
    fun uu___7 ->
      fun uu___6 ->
        fun uu___5 ->
          fun uu___4 ->
            fun uu___3 ->
              fun uu___2 ->
                fun uu___1 ->
                  fun uu___ ->
                    (fun g_then ->
                       fun e_then ->
                         fun c_then ->
                           fun e_then_typing ->
                             fun g_else ->
                               fun e_else ->
                                 fun c_else ->
                                   fun e_else_typing ->
                                     fun post ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___ ->
                                               match (c_then, c_else) with
                                               | (Pulse_Syntax_Base.C_STAtomic
                                                  (uu___1, obs1, uu___2),
                                                  Pulse_Syntax_Base.C_STAtomic
                                                  (uu___3, obs2, uu___4)) ->
                                                   FStar_Pervasives.Mkdtuple3
                                                     ((Pulse_Syntax_Base.C_STAtomic
                                                         ((Pulse_Syntax_Base.comp_inames
                                                             c_then),
                                                           (Pulse_Typing.join_obs
                                                              obs1 obs2),
                                                           (Pulse_Syntax_Base.st_comp_of_comp
                                                              c_then))),
                                                       (Pulse_Typing.T_Lift
                                                          (g_then, e_then,
                                                            c_then,
                                                            (Pulse_Syntax_Base.C_STAtomic
                                                               ((Pulse_Syntax_Base.comp_inames
                                                                   c_then),
                                                                 (Pulse_Typing.join_obs
                                                                    obs1 obs2),
                                                                 (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_then))),
                                                            e_then_typing,
                                                            (Pulse_Typing.Lift_Observability
                                                               (g_then,
                                                                 c_then,
                                                                 (Pulse_Typing.join_obs
                                                                    obs1 obs2))))),
                                                       (Pulse_Typing.T_Lift
                                                          (g_else, e_else,
                                                            c_else,
                                                            (Pulse_Syntax_Base.C_STAtomic
                                                               ((Pulse_Syntax_Base.comp_inames
                                                                   c_else),
                                                                 (Pulse_Typing.join_obs
                                                                    obs1 obs2),
                                                                 (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_else))),
                                                            e_else_typing,
                                                            (Pulse_Typing.Lift_Observability
                                                               (g_else,
                                                                 c_else,
                                                                 (Pulse_Typing.join_obs
                                                                    obs1 obs2))))))
                                               | uu___1 ->
                                                   FStar_Pervasives.Mkdtuple3
                                                     (c_then, e_then_typing,
                                                       e_else_typing))))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___