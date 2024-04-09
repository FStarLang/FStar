open Prims
let rec (join_comps :
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
  fun g_then ->
    fun e_then ->
      fun c_then ->
        fun e_then_typing ->
          fun g_else ->
            fun e_else ->
              fun c_else ->
                fun e_else_typing ->
                  fun post ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.JoinComp.fst"
                               (Prims.of_int (63)) (Prims.of_int (10))
                               (Prims.of_int (63)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.JoinComp.fst"
                               (Prims.of_int (65)) (Prims.of_int (2))
                               (Prims.of_int (86)) (Prims.of_int (49)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> g_then))
                      (fun uu___ ->
                         (fun g ->
                            match (c_then, c_else) with
                            | (Pulse_Syntax_Base.C_STAtomic
                               (uu___, obs1, uu___1),
                               Pulse_Syntax_Base.C_STAtomic
                               (uu___2, obs2, uu___3)) ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 ->
                                           FStar_Pervasives.Mkdtuple3
                                             ((Pulse_Syntax_Base.C_STAtomic
                                                 ((Pulse_Syntax_Base.comp_inames
                                                     c_then),
                                                   (Pulse_Typing.join_obs
                                                      obs1 obs2),
                                                   (Pulse_Syntax_Base.st_comp_of_comp
                                                      c_then))),
                                               (Pulse_Typing.T_Lift
                                                  (g_then, e_then, c_then,
                                                    (Pulse_Syntax_Base.C_STAtomic
                                                       ((Pulse_Syntax_Base.comp_inames
                                                           c_then),
                                                         (Pulse_Typing.join_obs
                                                            obs1 obs2),
                                                         (Pulse_Syntax_Base.st_comp_of_comp
                                                            c_then))),
                                                    e_then_typing,
                                                    (Pulse_Typing.Lift_Observability
                                                       (g_then, c_then,
                                                         (Pulse_Typing.join_obs
                                                            obs1 obs2))))),
                                               (Pulse_Typing.T_Lift
                                                  (g_else, e_else, c_else,
                                                    (Pulse_Syntax_Base.C_STAtomic
                                                       ((Pulse_Syntax_Base.comp_inames
                                                           c_else),
                                                         (Pulse_Typing.join_obs
                                                            obs1 obs2),
                                                         (Pulse_Syntax_Base.st_comp_of_comp
                                                            c_else))),
                                                    e_else_typing,
                                                    (Pulse_Typing.Lift_Observability
                                                       (g_else, c_else,
                                                         (Pulse_Typing.join_obs
                                                            obs1 obs2)))))))))
                            | (Pulse_Syntax_Base.C_STGhost (uu___, uu___1),
                               Pulse_Syntax_Base.C_STGhost (uu___2, uu___3))
                                ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 ->
                                           FStar_Pervasives.Mkdtuple3
                                             (c_then, e_then_typing,
                                               e_else_typing))))
                            | (Pulse_Syntax_Base.C_ST uu___,
                               Pulse_Syntax_Base.C_ST uu___1) ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           FStar_Pervasives.Mkdtuple3
                                             (c_then, e_then_typing,
                                               e_else_typing))))
                            | uu___ ->
                                Obj.magic
                                  (Obj.repr
                                     (match (c_then, c_else) with
                                      | (Pulse_Syntax_Base.C_STGhost
                                         (uu___1, uu___2),
                                         Pulse_Syntax_Base.C_STAtomic
                                         (uu___3, uu___4, uu___5)) ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.JoinComp.fst"
                                                     (Prims.of_int (79))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (79))
                                                     (Prims.of_int (39)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.JoinComp.fst"
                                                     (Prims.of_int (81))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (81))
                                                     (Prims.of_int (49)))))
                                            (Obj.magic
                                               (Pulse_Typing_Combinators.lift_ghost_atomic
                                                  g_then e_then c_then
                                                  e_then_typing))
                                            (fun uu___6 ->
                                               (fun d ->
                                                  Obj.magic
                                                    (join_comps g_then e_then
                                                       (Pulse_Typing_Combinators.st_ghost_as_atomic
                                                          c_then) d g_else
                                                       e_else c_else
                                                       e_else_typing post))
                                                 uu___6)
                                      | (Pulse_Syntax_Base.C_STAtomic
                                         (uu___1, uu___2, uu___3),
                                         Pulse_Syntax_Base.C_STGhost
                                         (uu___4, uu___5)) ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.JoinComp.fst"
                                                     (Prims.of_int (84))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (84))
                                                     (Prims.of_int (45)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.JoinComp.fst"
                                                     (Prims.of_int (86))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (86))
                                                     (Prims.of_int (49)))))
                                            (Obj.magic
                                               (Pulse_Typing_Combinators.lift_ghost_atomic
                                                  g_else e_else c_else
                                                  e_else_typing))
                                            (fun uu___6 ->
                                               (fun d ->
                                                  Obj.magic
                                                    (join_comps g_then e_then
                                                       c_then e_then_typing
                                                       g_else e_else
                                                       (Pulse_Typing_Combinators.st_ghost_as_atomic
                                                          c_else) d post))
                                                 uu___6)))) uu___)