open Prims
let (elim_pure_head : Pulse_Syntax_Base.term) =
  let elim_pure_explicit_lid =
    Pulse_Reflection_Util.mk_pulse_lib_core_lid "elim_pure_explicit" in
  Pulse_Syntax_Pure.tm_fvar (Pulse_Syntax_Base.as_fv elim_pure_explicit_lid)
let (elim_pure_head_ty : FStar_Reflection_Types.term) =
  let squash_p =
    Pulse_Reflection_Util.mk_squash Pulse_Syntax_Pure.u0
      (FStar_Reflection_Typing.bound_var Prims.int_zero) in
  let pure_p =
    Pulse_Reflection_Util.mk_pure
      (FStar_Reflection_Typing.bound_var Prims.int_zero) in
  let post =
    Pulse_Reflection_Util.mk_abs squash_p FStar_Reflection_V2_Data.Q_Explicit
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               Pulse_Reflection_Util.emp_lid))) in
  let cod =
    Pulse_Reflection_Util.mk_stt_ghost_comp Pulse_Syntax_Pure.u0 squash_p
      Pulse_Reflection_Util.emp_inames_tm pure_p post in
  Pulse_Reflection_Util.mk_arrow
    ((FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_FVar
           (FStar_Reflection_V2_Builtins.pack_fv
              FStar_Reflection_Const.prop_qn))),
      FStar_Reflection_V2_Data.Q_Explicit) cod
let (tm_fstar : Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.term) =
  fun t -> Pulse_Syntax_Base.tm_fstar t FStar_Range.range_0

let (mk_elim_pure : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term) =
  fun p ->
    let t =
      Pulse_Syntax_Base.Tm_STApp
        {
          Pulse_Syntax_Base.head = elim_pure_head;
          Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
          Pulse_Syntax_Base.arg = p
        } in
    Pulse_Typing.wr t
let (elim_pure_comp : Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.comp)
  =
  fun p ->
    let st =
      {
        Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u_zero;
        Pulse_Syntax_Base.res =
          (tm_fstar (Pulse_Reflection_Util.mk_squash Pulse_Syntax_Pure.u0 p));
        Pulse_Syntax_Base.pre = (Pulse_Syntax_Base.tm_pure (tm_fstar p));
        Pulse_Syntax_Base.post = Pulse_Syntax_Base.tm_emp
      } in
    Pulse_Syntax_Base.C_STGhost (Pulse_Syntax_Base.tm_emp_inames, st)
let (elim_pure_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.host_term ->
      unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun p ->
      fun p_prop ->
        Pulse_Typing.T_STApp
          (g, elim_pure_head, (tm_fstar FStar_Reflection_Typing.tm_prop),
            FStar_Pervasives_Native.None, (elim_pure_comp p), (tm_fstar p),
            (), ())
let (is_elim_pure :
  Pulse_Syntax_Base.term -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun vp ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match vp.Pulse_Syntax_Base.t with
               | Pulse_Syntax_Base.Tm_Pure
                   { Pulse_Syntax_Base.t = Pulse_Syntax_Base.Tm_FStar uu___1;
                     Pulse_Syntax_Base.range1 = uu___2;_}
                   -> true
               | uu___1 -> false))) uu___
let (mk :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
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
                       match v.Pulse_Syntax_Base.t with
                       | Pulse_Syntax_Base.Tm_Pure
                           {
                             Pulse_Syntax_Base.t = Pulse_Syntax_Base.Tm_FStar
                               pp;
                             Pulse_Syntax_Base.range1 = uu___1;_}
                           ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Mkdtuple4
                                (Pulse_Syntax_Base.ppname_default,
                                  (mk_elim_pure (tm_fstar pp)),
                                  (elim_pure_comp pp),
                                  (elim_pure_typing g pp ())))
                       | uu___1 -> FStar_Pervasives_Native.None))) uu___2
          uu___1 uu___
let (elim_pure_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
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
            Pulse_Checker_Prover_Base.add_elims g ctxt frame is_elim_pure mk
              () uvs
let (elim_pure :
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
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.ElimPure.fst"
                   (Prims.of_int (104)) (Prims.of_int (70))
                   (Prims.of_int (104)) (Prims.of_int (78)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.ElimPure.fst"
                   (Prims.of_int (104)) (Prims.of_int (81))
                   (Prims.of_int (109)) (Prims.of_int (62)))))
          (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
          (fun uu___ ->
             (fun ctxt_emp_typing ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.ElimPure.fst"
                              (Prims.of_int (106)) (Prims.of_int (4))
                              (Prims.of_int (106)) (Prims.of_int (58)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.ElimPure.fst"
                              (Prims.of_int (104)) (Prims.of_int (81))
                              (Prims.of_int (109)) (Prims.of_int (62)))))
                     (Obj.magic
                        (elim_pure_frame g ctxt Pulse_Syntax_Base.tm_emp ()
                           (Pulse_Typing_Env.mk_env
                              (Pulse_Typing_Env.fstar_env g))))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             match uu___ with
                             | FStar_Pervasives.Mkdtuple4
                                 (g', ctxt', ctxt'_emp_typing, k) ->
                                 FStar_Pervasives.Mkdtuple4
                                   (g', ctxt', (),
                                     (Pulse_Checker_Base.k_elab_equiv g g'
                                        (Pulse_Checker_Prover_Base.op_Star
                                           ctxt Pulse_Syntax_Base.tm_emp)
                                        ctxt
                                        (Pulse_Checker_Prover_Base.op_Star
                                           ctxt' Pulse_Syntax_Base.tm_emp)
                                        ctxt' k () ())))))) uu___)
let (elim_pure_pst :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ElimPure.fst"
                 (Prims.of_int (118)) (Prims.of_int (4)) (Prims.of_int (123))
                 (Prims.of_int (13)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ElimPure.fst"
                 (Prims.of_int (115)) (Prims.of_int (74))
                 (Prims.of_int (153)) (Prims.of_int (3)))))
        (Obj.magic
           (elim_pure_frame pst.Pulse_Checker_Prover_Base.pg
              (Pulse_Typing_Combinators.list_as_vprop
                 pst.Pulse_Checker_Prover_Base.remaining_ctxt)
              (Pulse_Checker_Prover_Base.op_Star
                 preamble.Pulse_Checker_Prover_Base.frame
                 (Pulse_Checker_Prover_Base.op_Array_Access
                    pst.Pulse_Checker_Prover_Base.ss
                    pst.Pulse_Checker_Prover_Base.solved)) ()
              pst.Pulse_Checker_Prover_Base.uvs))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                match uu___ with
                | FStar_Pervasives.Mkdtuple4 (g', remaining_ctxt', ty, k) ->
                    {
                      Pulse_Checker_Prover_Base.pg = g';
                      Pulse_Checker_Prover_Base.remaining_ctxt =
                        (Pulse_Typing_Combinators.vprop_as_list
                           remaining_ctxt');
                      Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing =
                        ();
                      Pulse_Checker_Prover_Base.uvs =
                        (pst.Pulse_Checker_Prover_Base.uvs);
                      Pulse_Checker_Prover_Base.ss =
                        (pst.Pulse_Checker_Prover_Base.ss);
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
                                 (Pulse_Typing_Combinators.list_as_vprop
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
                                 (Pulse_Typing_Combinators.list_as_vprop
                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                 (Pulse_Checker_Prover_Base.op_Star
                                    preamble.Pulse_Checker_Prover_Base.frame
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       pst.Pulse_Checker_Prover_Base.ss
                                       pst.Pulse_Checker_Prover_Base.solved)))
                              (Pulse_Checker_Prover_Base.op_Star
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Typing_Combinators.list_as_vprop
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
                                    pst.Pulse_Checker_Prover_Base.solved)) k
                              () ()));
                      Pulse_Checker_Prover_Base.goals_inv = ();
                      Pulse_Checker_Prover_Base.solved_inv = ()
                    }))