open Prims
let (check_comp :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      unit ->
        ((unit, unit, unit) Pulse_Typing.comp_typing, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      fun pre_typing ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Comp.fst" (Prims.of_int (22))
             (Prims.of_int (7)) (Prims.of_int (37)) (Prims.of_int (9)))
          (FStar_Range.mk_range "Pulse.Checker.Comp.fst" (Prims.of_int (39))
             (Prims.of_int (4)) (Prims.of_int (54)) (Prims.of_int (44)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun st ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                       (Prims.of_int (22)) (Prims.of_int (27))
                       (Prims.of_int (22)) (Prims.of_int (50)))
                    (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                       (Prims.of_int (22)) (Prims.of_int (7))
                       (Prims.of_int (37)) (Prims.of_int (9)))
                    (Obj.magic
                       (Pulse_Checker_Pure.check_universe g
                          st.Pulse_Syntax_Base.res))
                    (fun uu___1 ->
                       (fun uu___1 ->
                          match uu___1 with
                          | Prims.Mkdtuple2 (u, t_u) ->
                              if
                                Prims.op_Negation
                                  (Pulse_Syntax_Base.eq_univ u
                                     (Pulse_Syntax_Base.comp_u c))
                              then
                                Obj.magic
                                  (Pulse_Typing_Env.fail g
                                     FStar_Pervasives_Native.None
                                     "Unexpected universe")
                              else
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Comp.fst"
                                        (Prims.of_int (26))
                                        (Prims.of_int (18))
                                        (Prims.of_int (26))
                                        (Prims.of_int (25)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Comp.fst"
                                        (Prims.of_int (26))
                                        (Prims.of_int (28))
                                        (Prims.of_int (36))
                                        (Prims.of_int (11)))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           Pulse_Typing_Env.fresh g))
                                     (fun uu___3 ->
                                        (fun x ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Comp.fst"
                                                   (Prims.of_int (27))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (27))
                                                   (Prims.of_int (28)))
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Comp.fst"
                                                   (Prims.of_int (28))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (11)))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      Pulse_Syntax_Base.v_as_nv
                                                        x))
                                                (fun uu___3 ->
                                                   (fun px ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Comp.fst"
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (51)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Comp.fst"
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (54))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (11)))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 Pulse_Typing_Env.push_binding
                                                                   g x
                                                                   (FStar_Pervasives_Native.fst
                                                                    px)
                                                                   st.Pulse_Syntax_Base.res))
                                                           (fun uu___3 ->
                                                              (fun gx ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (88)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_term
                                                                    gx
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) px)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (ty,
                                                                    post_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    Pulse_Syntax_Base.Tm_VProp)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Ill-typed postcondition"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.STC
                                                                    (g, st,
                                                                    x, (),
                                                                    (), ())))))
                                                                    uu___3)))
                                                                uu___3)))
                                                     uu___3))) uu___3)))
                         uu___1)))
          (fun uu___ ->
             (fun check_st_comp ->
                match c with
                | Pulse_Syntax_Base.C_ST st ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                            (Prims.of_int (41)) (Prims.of_int (16))
                            (Prims.of_int (41)) (Prims.of_int (32)))
                         (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                            (Prims.of_int (42)) (Prims.of_int (6))
                            (Prims.of_int (42)) (Prims.of_int (19)))
                         (Obj.magic (check_st_comp st))
                         (fun stc ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> Pulse_Typing.CT_ST (g, st, stc))))
                | Pulse_Syntax_Base.C_STAtomic (i, st) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                            (Prims.of_int (44)) (Prims.of_int (16))
                            (Prims.of_int (44)) (Prims.of_int (32)))
                         (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                            (Prims.of_int (44)) (Prims.of_int (35))
                            (Prims.of_int (48)) (Prims.of_int (45)))
                         (Obj.magic (check_st_comp st))
                         (fun uu___ ->
                            (fun stc ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Comp.fst"
                                       (Prims.of_int (45))
                                       (Prims.of_int (31))
                                       (Prims.of_int (45))
                                       (Prims.of_int (50)))
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Comp.fst"
                                       (Prims.of_int (44))
                                       (Prims.of_int (35))
                                       (Prims.of_int (48))
                                       (Prims.of_int (45)))
                                    (Obj.magic
                                       (Pulse_Checker_Pure.core_check_term g
                                          i))
                                    (fun uu___ ->
                                       (fun uu___ ->
                                          match uu___ with
                                          | Prims.Mkdtuple2 (ty, i_typing) ->
                                              if
                                                Prims.op_Negation
                                                  (Pulse_Syntax_Base.eq_tm ty
                                                     Pulse_Syntax_Base.Tm_Inames)
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (Pulse_Typing_Env.fail g
                                                        FStar_Pervasives_Native.None
                                                        "Ill-typed inames"))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Typing.CT_STAtomic
                                                             (g, i, st, (),
                                                               stc))))) uu___)))
                              uu___))
                | Pulse_Syntax_Base.C_STGhost (i, st) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                            (Prims.of_int (50)) (Prims.of_int (16))
                            (Prims.of_int (50)) (Prims.of_int (32)))
                         (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                            (Prims.of_int (50)) (Prims.of_int (35))
                            (Prims.of_int (54)) (Prims.of_int (44)))
                         (Obj.magic (check_st_comp st))
                         (fun uu___ ->
                            (fun stc ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Comp.fst"
                                       (Prims.of_int (51))
                                       (Prims.of_int (31))
                                       (Prims.of_int (51))
                                       (Prims.of_int (50)))
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Comp.fst"
                                       (Prims.of_int (50))
                                       (Prims.of_int (35))
                                       (Prims.of_int (54))
                                       (Prims.of_int (44)))
                                    (Obj.magic
                                       (Pulse_Checker_Pure.core_check_term g
                                          i))
                                    (fun uu___ ->
                                       (fun uu___ ->
                                          match uu___ with
                                          | Prims.Mkdtuple2 (ty, i_typing) ->
                                              if
                                                Prims.op_Negation
                                                  (Pulse_Syntax_Base.eq_tm ty
                                                     Pulse_Syntax_Base.Tm_Inames)
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (Pulse_Typing_Env.fail g
                                                        FStar_Pervasives_Native.None
                                                        "Ill-typed inames"))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Typing.CT_STGhost
                                                             (g, i, st, (),
                                                               stc))))) uu___)))
                              uu___))) uu___)