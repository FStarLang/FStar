open Prims
let (should_elim_exists :
  Pulse_Syntax_Base.slprop ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun v ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match Pulse_Syntax_Pure.inspect_term v with
               | Pulse_Syntax_Pure.Tm_ExistsSL (uu___1, uu___2, uu___3) ->
                   true
               | uu___1 -> false))) uu___
let (mk :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      unit ->
        ((Pulse_Syntax_Base.ppname, Pulse_Syntax_Base.st_term,
           Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun v ->
             fun v_typing ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       match Pulse_Syntax_Pure.inspect_term v with
                       | Pulse_Syntax_Pure.Tm_ExistsSL
                           (u,
                            { Pulse_Syntax_Base.binder_ty = t;
                              Pulse_Syntax_Base.binder_ppname = nm;
                              Pulse_Syntax_Base.binder_attrs = uu___1;_},
                            p)
                           ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Mkdtuple4
                                (nm,
                                  (Pulse_Typing.wtag
                                     (FStar_Pervasives_Native.Some
                                        Pulse_Syntax_Base.STT_Ghost)
                                     (Pulse_Syntax_Base.Tm_ElimExists
                                        {
                                          Pulse_Syntax_Base.p4 =
                                            (Pulse_Syntax_Pure.tm_exists_sl
                                               (Pulse_Syntax_Base.comp_u
                                                  (Pulse_Typing.comp_elim_exists
                                                     u t p
                                                     (nm,
                                                       (Pulse_Typing_Env.fresh
                                                          g))))
                                               (Pulse_Syntax_Base.as_binder t)
                                               p)
                                        })),
                                  (Pulse_Typing.comp_elim_exists u t p
                                     (nm, (Pulse_Typing_Env.fresh g))),
                                  (Pulse_Typing.T_ElimExists
                                     (g,
                                       (Pulse_Syntax_Base.comp_u
                                          (Pulse_Typing.comp_elim_exists u t
                                             p
                                             (nm, (Pulse_Typing_Env.fresh g)))),
                                       t, p, (Pulse_Typing_Env.fresh g), (),
                                       ()))))
                       | uu___1 -> FStar_Pervasives_Native.None))) uu___2
          uu___1 uu___
let (elim_exists_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      Pulse_Syntax_Base.slprop ->
        unit ->
          Pulse_Typing_Env.env ->
            ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
               (unit, unit, unit, unit)
                 Pulse_Checker_Base.continuation_elaborator)
               FStar_Pervasives.dtuple4,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun ctxt_frame_typing ->
          fun uvs ->
            Pulse_Checker_Prover_Base.add_elims g ctxt frame
              should_elim_exists mk () uvs
let (elim_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
           (unit, unit, unit, unit)
             Pulse_Checker_Base.continuation_elaborator)
           FStar_Pervasives.dtuple4,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        let uu___ =
          elim_exists_frame g ctxt Pulse_Syntax_Pure.tm_emp ()
            (Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.ElimExists.fst"
                   (Prims.of_int (69)) (Prims.of_int (4)) (Prims.of_int (69))
                   (Prims.of_int (60)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.ElimExists.fst"
                   (Prims.of_int (67)) (Prims.of_int (85))
                   (Prims.of_int (72)) (Prims.of_int (62)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 ->
                  match uu___1 with
                  | FStar_Pervasives.Mkdtuple4
                      (g', ctxt', ctxt'_emp_typing, k) ->
                      FStar_Pervasives.Mkdtuple4
                        (g', ctxt', (),
                          (Pulse_Checker_Base.k_elab_equiv g g'
                             (Pulse_Checker_Prover_Base.op_Star ctxt
                                Pulse_Syntax_Pure.tm_emp) ctxt
                             (Pulse_Checker_Prover_Base.op_Star ctxt'
                                Pulse_Syntax_Pure.tm_emp) ctxt' k () ()))))
let (elim_exists_pst :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_List_Tot_Base.existsb
                  (fun t ->
                     Pulse_Syntax_Pure.uu___is_Tm_ExistsSL
                       (Pulse_Syntax_Pure.inspect_term t))
                  pst.Pulse_Checker_Prover_Base.remaining_ctxt)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ElimExists.fst"
                 (Prims.of_int (80)) (Prims.of_int (13)) (Prims.of_int (80))
                 (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ElimExists.fst"
                 (Prims.of_int (80)) (Prims.of_int (92)) (Prims.of_int (120))
                 (Prims.of_int (3))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun prog ->
              let uu___1 =
                elim_exists_frame pst.Pulse_Checker_Prover_Base.pg
                  (Pulse_Syntax_Pure.list_as_slprop
                     pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                  (Pulse_Checker_Prover_Base.op_Star
                     preamble.Pulse_Checker_Prover_Base.frame
                     (Pulse_Checker_Prover_Base.op_Array_Access
                        pst.Pulse_Checker_Prover_Base.ss
                        pst.Pulse_Checker_Prover_Base.solved)) ()
                  pst.Pulse_Checker_Prover_Base.uvs in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.ElimExists.fst"
                            (Prims.of_int (83)) (Prims.of_int (4))
                            (Prims.of_int (88)) (Prims.of_int (13)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.ElimExists.fst"
                            (Prims.of_int (80)) (Prims.of_int (92))
                            (Prims.of_int (120)) (Prims.of_int (3)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           match uu___2 with
                           | FStar_Pervasives.Mkdtuple4
                               (g', remaining_ctxt', ty, k) ->
                               {
                                 Pulse_Checker_Prover_Base.pg = g';
                                 Pulse_Checker_Prover_Base.remaining_ctxt =
                                   (Pulse_Syntax_Pure.slprop_as_list
                                      remaining_ctxt');
                                 Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                   = ();
                                 Pulse_Checker_Prover_Base.uvs =
                                   (pst.Pulse_Checker_Prover_Base.uvs);
                                 Pulse_Checker_Prover_Base.ss =
                                   (pst.Pulse_Checker_Prover_Base.ss);
                                 Pulse_Checker_Prover_Base.nts =
                                   FStar_Pervasives_Native.None;
                                 Pulse_Checker_Prover_Base.solved =
                                   (pst.Pulse_Checker_Prover_Base.solved);
                                 Pulse_Checker_Prover_Base.unsolved =
                                   (pst.Pulse_Checker_Prover_Base.unsolved);
                                 Pulse_Checker_Prover_Base.k =
                                   (Pulse_Checker_Base.k_elab_trans
                                      preamble.Pulse_Checker_Prover_Base.g0
                                      (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__pg
                                         preamble pst) g'
                                      (Pulse_Checker_Prover_Base.op_Star
                                         preamble.Pulse_Checker_Prover_Base.ctxt
                                         preamble.Pulse_Checker_Prover_Base.frame)
                                      (Pulse_Checker_Prover_Base.op_Star
                                         (Pulse_Checker_Prover_Base.op_Star
                                            (Pulse_Syntax_Pure.list_as_slprop
                                               (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__remaining_ctxt
                                                  preamble pst))
                                            preamble.Pulse_Checker_Prover_Base.frame)
                                         (Pulse_Checker_Prover_Base.op_Array_Access
                                            (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__ss
                                               preamble pst)
                                            (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__solved
                                               preamble pst)))
                                      (Pulse_Checker_Prover_Base.op_Star
                                         (Pulse_Checker_Prover_Base.op_Star
                                            remaining_ctxt'
                                            preamble.Pulse_Checker_Prover_Base.frame)
                                         (Pulse_Checker_Prover_Base.op_Array_Access
                                            pst.Pulse_Checker_Prover_Base.ss
                                            pst.Pulse_Checker_Prover_Base.solved))
                                      pst.Pulse_Checker_Prover_Base.k
                                      (Pulse_Checker_Base.k_elab_equiv
                                         pst.Pulse_Checker_Prover_Base.pg g'
                                         (Pulse_Checker_Prover_Base.op_Star
                                            (Pulse_Syntax_Pure.list_as_slprop
                                               pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                            (Pulse_Checker_Prover_Base.op_Star
                                               preamble.Pulse_Checker_Prover_Base.frame
                                               (Pulse_Checker_Prover_Base.op_Array_Access
                                                  pst.Pulse_Checker_Prover_Base.ss
                                                  pst.Pulse_Checker_Prover_Base.solved)))
                                         (Pulse_Checker_Prover_Base.op_Star
                                            (Pulse_Checker_Prover_Base.op_Star
                                               (Pulse_Syntax_Pure.list_as_slprop
                                                  pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                               preamble.Pulse_Checker_Prover_Base.frame)
                                            (Pulse_Checker_Prover_Base.op_Array_Access
                                               pst.Pulse_Checker_Prover_Base.ss
                                               pst.Pulse_Checker_Prover_Base.solved))
                                         (Pulse_Checker_Prover_Base.op_Star
                                            remaining_ctxt'
                                            (Pulse_Checker_Prover_Base.op_Star
                                               preamble.Pulse_Checker_Prover_Base.frame
                                               (Pulse_Checker_Prover_Base.op_Array_Access
                                                  pst.Pulse_Checker_Prover_Base.ss
                                                  pst.Pulse_Checker_Prover_Base.solved)))
                                         (Pulse_Checker_Prover_Base.op_Star
                                            (Pulse_Checker_Prover_Base.op_Star
                                               remaining_ctxt'
                                               preamble.Pulse_Checker_Prover_Base.frame)
                                            (Pulse_Checker_Prover_Base.op_Array_Access
                                               pst.Pulse_Checker_Prover_Base.ss
                                               pst.Pulse_Checker_Prover_Base.solved))
                                         k () ()));
                                 Pulse_Checker_Prover_Base.goals_inv = ();
                                 Pulse_Checker_Prover_Base.solved_inv = ();
                                 Pulse_Checker_Prover_Base.progress = prog;
                                 Pulse_Checker_Prover_Base.allow_ambiguous =
                                   (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                               })))) uu___1)