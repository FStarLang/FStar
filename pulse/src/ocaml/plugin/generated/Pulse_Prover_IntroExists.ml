open Prims
let (intro_exists_sub_prover_state :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              (Pulse_Syntax_Base.var, Pulse_Prover_Common.preamble,
                unit Pulse_Prover_Common.prover_state)
                FStar_Pervasives.dtuple3)
  =
  fun preamble ->
    fun p ->
      fun u ->
        fun b ->
          fun body ->
            fun exists_typing ->
              let g0 = preamble.Pulse_Prover_Common.g0 in
              let x =
                Pulse_Typing_Env.fresh
                  (Pulse_Typing_Env.push_env g0
                     preamble.Pulse_Prover_Common.uvs) in
              let uvs =
                Pulse_Prover_Util.psubst_env preamble.Pulse_Prover_Common.g0
                  (Pulse_Prover_Util.filter_ss
                     preamble.Pulse_Prover_Common.g0
                     preamble.Pulse_Prover_Common.uvs
                     p.Pulse_Prover_Common.ss) p.Pulse_Prover_Common.ss in
              let uvs1 =
                Pulse_Typing_Env.push_binding uvs x
                  b.Pulse_Syntax_Base.binder_ty in
              let preamble_sub =
                {
                  Pulse_Prover_Common.g0 = g0;
                  Pulse_Prover_Common.ctxt =
                    (Pulse_Checker_VPropEquiv.list_as_vprop
                       p.Pulse_Prover_Common.remaining_ctxt);
                  Pulse_Prover_Common.ctxt_typing = ();
                  Pulse_Prover_Common.t =
                    (Pulse_Typing.wr
                       (Pulse_Syntax_Base.Tm_IntroExists
                          {
                            Pulse_Syntax_Base.erased = false;
                            Pulse_Syntax_Base.p2 =
                              (Pulse_Syntax_Base.Tm_ExistsSL (u, b, body));
                            Pulse_Syntax_Base.witnesses =
                              [Pulse_Syntax_Pure.null_var x];
                            Pulse_Syntax_Base.should_check1 =
                              Pulse_Syntax_Base.should_check_false
                          }));
                  Pulse_Prover_Common.c =
                    (Pulse_Typing.comp_intro_exists u b body
                       (Pulse_Syntax_Pure.null_var x));
                  Pulse_Prover_Common.uvs = uvs1
                } in
              let ss = Pulse_Prover_Substs.empty g0 in
              let solved_goals = Pulse_Syntax_Base.Tm_Emp in
              let unsolved_goals =
                Pulse_Checker_VPropEquiv.vprop_as_list
                  (Pulse_Syntax_Base.comp_pre
                     preamble_sub.Pulse_Prover_Common.c) in
              let remaining_ctxt =
                Pulse_Checker_VPropEquiv.vprop_as_list
                  preamble_sub.Pulse_Prover_Common.ctxt in
              let t_typing =
                Pulse_Typing.T_IntroExists
                  ((Pulse_Prover_Common.pst_env g0
                      preamble_sub.Pulse_Prover_Common.uvs ss), u, b, body,
                    (Pulse_Syntax_Pure.null_var x), (), (), ()) in
              let t_typing1 = t_typing in
              let uu___ =
                Pulse_Prover_Util.idem_steps
                  (Pulse_Prover_Common.pst_env g0
                     preamble_sub.Pulse_Prover_Common.uvs ss)
                  (Pulse_Checker_VPropEquiv.list_as_vprop remaining_ctxt) in
              match uu___ with
              | Prims.Mkdtuple2 (steps, steps_typing) ->
                  let steps_typing1 = steps_typing in
                  FStar_Pervasives.Mkdtuple3
                    (x, preamble_sub,
                      {
                        Pulse_Prover_Common.ss = ss;
                        Pulse_Prover_Common.solved_goals = solved_goals;
                        Pulse_Prover_Common.unsolved_goals = unsolved_goals;
                        Pulse_Prover_Common.remaining_ctxt = remaining_ctxt;
                        Pulse_Prover_Common.steps = steps;
                        Pulse_Prover_Common.t_typing = t_typing1;
                        Pulse_Prover_Common.unsolved_goals_typing = ();
                        Pulse_Prover_Common.remaining_ctxt_typing = ();
                        Pulse_Prover_Common.steps_typing = steps_typing1;
                        Pulse_Prover_Common.c_pre_inv = ();
                        Pulse_Prover_Common.solved_goals_closed = ()
                      })
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (intro_exists_step :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                Pulse_Prover_Common.prover_t ->
                  (unit Pulse_Prover_Common.prover_state
                     FStar_Pervasives_Native.option,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun p ->
      fun u ->
        fun b ->
          fun body ->
            fun unsolved_goals' ->
              fun uu___ ->
                fun prover ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Prover.IntroExists.fst"
                       (Prims.of_int (131)) (Prims.of_int (11))
                       (Prims.of_int (131)) (Prims.of_int (22)))
                    (FStar_Range.mk_range "Pulse.Prover.IntroExists.fst"
                       (Prims.of_int (131)) (Prims.of_int (25))
                       (Prims.of_int (336)) (Prims.of_int (13)))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> preamble.Pulse_Prover_Common.g0))
                    (fun uu___1 ->
                       (fun g0 ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "Pulse.Prover.IntroExists.fst"
                                  (Prims.of_int (132)) (Prims.of_int (32))
                                  (Prims.of_int (134)) (Prims.of_int (14)))
                               (FStar_Range.mk_range
                                  "Pulse.Prover.IntroExists.fst"
                                  (Prims.of_int (131)) (Prims.of_int (25))
                                  (Prims.of_int (336)) (Prims.of_int (13)))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     intro_exists_sub_prover_state preamble p
                                       u b body ()))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | FStar_Pervasives.Mkdtuple3
                                         (x, s_preamble, sp) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.IntroExists.fst"
                                                 (Prims.of_int (136))
                                                 (Prims.of_int (11))
                                                 (Prims.of_int (136))
                                                 (Prims.of_int (20)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.IntroExists.fst"
                                                 (Prims.of_int (137))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (336))
                                                 (Prims.of_int (13)))
                                              (Obj.magic
                                                 (prover s_preamble sp))
                                              (fun sp1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      match sp1 with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          sp2 ->
                                                          if
                                                            FStar_Set.mem x
                                                              (Pulse_Prover_Substs.dom
                                                                 s_preamble.Pulse_Prover_Common.g0
                                                                 sp2.Pulse_Prover_Common.ss)
                                                          then
                                                            (match Pulse_Prover_Util.apply_partial_subs
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    p.Pulse_Prover_Common.steps
                                                                    (Pulse_Prover_Util.ghost_comp
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    p.Pulse_Prover_Common.remaining_ctxt),
                                                                    (p.Pulse_Prover_Common.solved_goals))))
                                                                    (Pulse_Prover_Util.psubst_env
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Util.filter_ss
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    preamble.Pulse_Prover_Common.uvs
                                                                    p.Pulse_Prover_Common.ss)
                                                                    p.Pulse_Prover_Common.ss)
                                                                    (Pulse_Prover_Substs.diff
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.singleton
                                                                    g0 x
                                                                    (Pulse_Prover_Substs.lookup
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    x)))
                                                                    p.Pulse_Prover_Common.steps_typing
                                                             with
                                                             | Prims.Mkdtuple2
                                                                 (uu___3,
                                                                  pt_typing)
                                                                 ->
                                                                 (match 
                                                                    Pulse_Prover_Util.apply_partial_subs_veq
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Substs.subst_term
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    p.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    preamble.Pulse_Prover_Common.c))
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    p.Pulse_Prover_Common.unsolved_goals),
                                                                    (p.Pulse_Prover_Common.solved_goals)))
                                                                    (Pulse_Prover_Util.psubst_env
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Util.filter_ss
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    preamble.Pulse_Prover_Common.uvs
                                                                    p.Pulse_Prover_Common.ss)
                                                                    p.Pulse_Prover_Common.ss)
                                                                    (Pulse_Prover_Substs.diff
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.singleton
                                                                    g0 x
                                                                    (Pulse_Prover_Substs.lookup
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    x))) ()
                                                                  with
                                                                  | Prims.Mkdtuple2
                                                                    (uu___4,
                                                                    c_pre_inv)
                                                                    ->
                                                                    (match 
                                                                    Pulse_Prover_Util.apply_partial_subs
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Substs.subst_st_term
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    p.Pulse_Prover_Common.ss
                                                                    preamble.Pulse_Prover_Common.t)
                                                                    (Pulse_Prover_Substs.subst_comp
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    p.Pulse_Prover_Common.ss
                                                                    preamble.Pulse_Prover_Common.c)
                                                                    (Pulse_Prover_Util.psubst_env
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Util.filter_ss
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    preamble.Pulse_Prover_Common.uvs
                                                                    p.Pulse_Prover_Common.ss)
                                                                    p.Pulse_Prover_Common.ss)
                                                                    (Pulse_Prover_Substs.diff
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.singleton
                                                                    g0 x
                                                                    (Pulse_Prover_Substs.lookup
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    x)))
                                                                    p.Pulse_Prover_Common.t_typing
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (uu___5,
                                                                    t_typing)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (Pulse_Prover_Substs.push
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    p.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.diff
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.singleton
                                                                    g0 x
                                                                    (Pulse_Prover_Substs.lookup
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    x))));
                                                                    Pulse_Prover_Common.solved_goals
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((Pulse_Prover_Substs.subst_term
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Substs.diff
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.singleton
                                                                    g0 x
                                                                    (Pulse_Prover_Substs.lookup
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    x)))
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, b,
                                                                    body))),
                                                                    (p.Pulse_Prover_Common.solved_goals)));
                                                                    Pulse_Prover_Common.unsolved_goals
                                                                    =
                                                                    (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    (Pulse_Prover_Substs.subst_term
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Substs.diff
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Substs.singleton
                                                                    g0 x
                                                                    (Pulse_Prover_Substs.lookup
                                                                    s_preamble.Pulse_Prover_Common.g0
                                                                    sp2.Pulse_Prover_Common.ss
                                                                    x)))
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved_goals')));
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    sp2.Pulse_Prover_Common.remaining_ctxt));
                                                                    Pulse_Prover_Common.steps
                                                                    =
                                                                    (Prims.magic
                                                                    ());
                                                                    Pulse_Prover_Common.t_typing
                                                                    =
                                                                    (coerce_eq
                                                                    t_typing
                                                                    ());
                                                                    Pulse_Prover_Common.unsolved_goals_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.remaining_ctxt_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.steps_typing
                                                                    =
                                                                    (coerce_eq
                                                                    (Prims.magic
                                                                    ()) ());
                                                                    Pulse_Prover_Common.c_pre_inv
                                                                    = ();
                                                                    Pulse_Prover_Common.solved_goals_closed
                                                                    = ()
                                                                    })))
                                                          else
                                                            FStar_Pervasives_Native.None))))
                                    uu___1))) uu___1)
let (intro_exists_prover_step : Pulse_Prover_Common.prover_step_t) =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> Prims.magic ()))