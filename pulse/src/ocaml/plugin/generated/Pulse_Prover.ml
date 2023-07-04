open Prims
let (unsolved_equiv_pst :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.vprop Prims.list ->
        unit -> unit Pulse_Prover_Common.prover_state)
  =
  fun preamble ->
    fun pst ->
      fun unsolved' ->
        fun d ->
          {
            Pulse_Prover_Common.pg = (pst.Pulse_Prover_Common.pg);
            Pulse_Prover_Common.remaining_ctxt =
              (pst.Pulse_Prover_Common.remaining_ctxt);
            Pulse_Prover_Common.remaining_ctxt_frame_typing = ();
            Pulse_Prover_Common.uvs = (pst.Pulse_Prover_Common.uvs);
            Pulse_Prover_Common.ss = (pst.Pulse_Prover_Common.ss);
            Pulse_Prover_Common.solved = (pst.Pulse_Prover_Common.solved);
            Pulse_Prover_Common.unsolved = unsolved';
            Pulse_Prover_Common.solved_typing = ();
            Pulse_Prover_Common.k = (pst.Pulse_Prover_Common.k);
            Pulse_Prover_Common.goals_inv = ()
          }
let (remaining_ctxt_equiv_pst :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.vprop Prims.list ->
        unit -> unit Pulse_Prover_Common.prover_state)
  =
  fun preamble ->
    fun pst ->
      fun remaining_ctxt' ->
        fun d ->
          {
            Pulse_Prover_Common.pg = (pst.Pulse_Prover_Common.pg);
            Pulse_Prover_Common.remaining_ctxt = remaining_ctxt';
            Pulse_Prover_Common.remaining_ctxt_frame_typing = ();
            Pulse_Prover_Common.uvs = (pst.Pulse_Prover_Common.uvs);
            Pulse_Prover_Common.ss = (pst.Pulse_Prover_Common.ss);
            Pulse_Prover_Common.solved = (pst.Pulse_Prover_Common.solved);
            Pulse_Prover_Common.unsolved = (pst.Pulse_Prover_Common.unsolved);
            Pulse_Prover_Common.solved_typing = ();
            Pulse_Prover_Common.k =
              (Pulse_Prover_Common.k_elab_equiv
                 preamble.Pulse_Prover_Common.g0
                 (Pulse_Prover_Common.__proj__Mkprover_state__item__pg
                    preamble pst)
                 (Pulse_Prover_Common.op_Star
                    preamble.Pulse_Prover_Common.ctxt
                    preamble.Pulse_Prover_Common.frame)
                 (Pulse_Prover_Common.op_Star
                    preamble.Pulse_Prover_Common.ctxt
                    preamble.Pulse_Prover_Common.frame)
                 (Pulse_Prover_Common.op_Star
                    (Pulse_Prover_Common.op_Star
                       (Pulse_Checker_VPropEquiv.list_as_vprop
                          (Pulse_Prover_Common.__proj__Mkprover_state__item__remaining_ctxt
                             preamble pst))
                       preamble.Pulse_Prover_Common.frame)
                    (Pulse_Prover_Common.op_Array_Access
                       (Pulse_Prover_Common.__proj__Mkprover_state__item__ss
                          preamble pst)
                       (Pulse_Prover_Common.__proj__Mkprover_state__item__solved
                          preamble pst)))
                 (Pulse_Prover_Common.op_Star
                    (Pulse_Prover_Common.op_Star
                       (Pulse_Checker_VPropEquiv.list_as_vprop
                          remaining_ctxt') preamble.Pulse_Prover_Common.frame)
                    (Pulse_Prover_Common.op_Array_Access
                       pst.Pulse_Prover_Common.ss
                       pst.Pulse_Prover_Common.solved))
                 pst.Pulse_Prover_Common.k () ());
            Pulse_Prover_Common.goals_inv = ()
          }
let rec (collect_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop Prims.list,
        Pulse_Syntax_Base.vprop Prims.list, unit) FStar_Pervasives.dtuple3)
  =
  fun g ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives.Mkdtuple3 ([], [], ())
      | hd::tl ->
          let uu___ = collect_exists g tl in
          (match uu___ with
           | FStar_Pervasives.Mkdtuple3 (exs, rest, uu___1) ->
               (match hd.Pulse_Syntax_Base.t with
                | Pulse_Syntax_Base.Tm_ExistsSL (uu___2, uu___3, uu___4) ->
                    FStar_Pervasives.Mkdtuple3 ((hd :: exs), rest, ())
                | uu___2 ->
                    FStar_Pervasives.Mkdtuple3 (exs, (hd :: rest), ())))
let rec (collect_pures :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop Prims.list,
        Pulse_Syntax_Base.vprop Prims.list, unit) FStar_Pervasives.dtuple3)
  =
  fun g ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives.Mkdtuple3 ([], [], ())
      | hd::tl ->
          let uu___ = collect_pures g tl in
          (match uu___ with
           | FStar_Pervasives.Mkdtuple3 (pures, rest, uu___1) ->
               (match hd.Pulse_Syntax_Base.t with
                | Pulse_Syntax_Base.Tm_Pure uu___2 ->
                    FStar_Pervasives.Mkdtuple3 ((hd :: pures), rest, ())
                | uu___2 ->
                    FStar_Pervasives.Mkdtuple3 (pures, (hd :: rest), ())))
let rec (match_q :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          unit ->
            Prims.nat ->
              (unit Pulse_Prover_Common.prover_state
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun preamble ->
                 fun pst ->
                   fun q ->
                     fun unsolved' ->
                       fun uu___ ->
                         fun i ->
                           if
                             (FStar_List_Tot_Base.length
                                pst.Pulse_Prover_Common.remaining_ctxt)
                               = Prims.int_zero
                           then
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pervasives_Native.None)))
                           else
                             Obj.magic
                               (Obj.repr
                                  (if
                                     i =
                                       (FStar_List_Tot_Base.length
                                          pst.Pulse_Prover_Common.remaining_ctxt)
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pervasives_Native.None))
                                   else
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.fst"
                                                   (Prims.of_int (75))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (75))
                                                   (Prims.of_int (35)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.fst"
                                                   (Prims.of_int (75))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (84))
                                                   (Prims.of_int (38)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_List_Tot_Base.hd
                                                  pst.Pulse_Prover_Common.remaining_ctxt))
                                          (fun uu___3 ->
                                             (fun p ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.fst"
                                                              (Prims.of_int (77))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (77))
                                                              (Prims.of_int (69)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.fst"
                                                              (Prims.of_int (78))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (84))
                                                              (Prims.of_int (38)))))
                                                     (Obj.magic
                                                        (Pulse_Prover_Match.match_step
                                                           preamble pst p
                                                           (FStar_List_Tot_Base.tl
                                                              pst.Pulse_Prover_Common.remaining_ctxt)
                                                           q unsolved' ()))
                                                     (fun uu___3 ->
                                                        (fun pst_opt ->
                                                           match pst_opt with
                                                           | FStar_Pervasives_Native.Some
                                                               pst1 ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    pst1)))
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    remaining_ctxt_equiv_pst
                                                                    preamble
                                                                    pst
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.tl
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    [
                                                                    FStar_List_Tot_Base.hd
                                                                    pst.Pulse_Prover_Common.remaining_ctxt])
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun pst1
                                                                    ->
                                                                    Obj.magic
                                                                    (match_q
                                                                    preamble
                                                                    pst1 q
                                                                    unsolved'
                                                                    ()
                                                                    (i +
                                                                    Prims.int_one)))
                                                                    uu___3))))
                                                          uu___3))) uu___3)))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let rec (prover :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      (unit Pulse_Prover_Common.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun preamble ->
         fun pst0 ->
           match pst0.Pulse_Prover_Common.unsolved with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> pst0)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Prover.fst"
                                (Prims.of_int (95)) (Prims.of_int (14))
                                (Prims.of_int (95)) (Prims.of_int (45)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Prover.fst"
                                (Prims.of_int (95)) (Prims.of_int (48))
                                (Prims.of_int (113)) (Prims.of_int (32)))))
                       (Obj.magic
                          (Pulse_Prover_ElimExists.elim_exists_pst preamble
                             pst0))
                       (fun uu___1 ->
                          (fun pst ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Prover.fst"
                                           (Prims.of_int (96))
                                           (Prims.of_int (14))
                                           (Prims.of_int (96))
                                           (Prims.of_int (40)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Prover.fst"
                                           (Prims.of_int (96))
                                           (Prims.of_int (43))
                                           (Prims.of_int (113))
                                           (Prims.of_int (32)))))
                                  (Obj.magic
                                     (Pulse_Prover_ElimPure.elim_pure_pst
                                        preamble pst))
                                  (fun uu___1 ->
                                     (fun pst1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Prover.fst"
                                                      (Prims.of_int (98))
                                                      (Prims.of_int (29))
                                                      (Prims.of_int (98))
                                                      (Prims.of_int (82)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Prover.fst"
                                                      (Prims.of_int (96))
                                                      (Prims.of_int (43))
                                                      (Prims.of_int (113))
                                                      (Prims.of_int (32)))))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   collect_exists
                                                     (Pulse_Typing_Env.push_env
                                                        pst1.Pulse_Prover_Common.pg
                                                        pst1.Pulse_Prover_Common.uvs)
                                                     pst1.Pulse_Prover_Common.unsolved))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | FStar_Pervasives.Mkdtuple3
                                                       (exs, rest, d) ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (49)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (32)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  unsolved_equiv_pst
                                                                    preamble
                                                                    pst1
                                                                    (
                                                                    FStar_List_Tot_Base.op_At
                                                                    exs rest)
                                                                    ()))
                                                            (fun uu___2 ->
                                                               (fun pst2 ->
                                                                  match 
                                                                    pst2.Pulse_Prover_Common.unsolved
                                                                  with
                                                                  | {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, b,
                                                                    body);
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___2;_}::unsolved'
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Prover_IntroExists.intro_exists
                                                                    preamble
                                                                    pst2 u b
                                                                    body
                                                                    unsolved'
                                                                    () prover)
                                                                  | uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    collect_pures
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst2.Pulse_Prover_Common.pg
                                                                    pst2.Pulse_Prover_Common.uvs)
                                                                    pst2.Pulse_Prover_Common.unsolved))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (pures,
                                                                    rest1,
                                                                    d1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    unsolved_equiv_pst
                                                                    preamble
                                                                    pst2
                                                                    (FStar_List_Tot_Base.op_At
                                                                    rest1
                                                                    pures) ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun pst3
                                                                    ->
                                                                    match 
                                                                    pst3.Pulse_Prover_Common.unsolved
                                                                    with
                                                                    | 
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    uu___4;
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___5;_}::tl
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    pst3.Pulse_Prover_Common.pg
                                                                    FStar_Pervasives_Native.None
                                                                    "intro pure not implemented yet")
                                                                    | 
                                                                    q::tl ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (match_q
                                                                    preamble
                                                                    pst3 q tl
                                                                    ()
                                                                    Prims.int_zero))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pst_opt
                                                                    ->
                                                                    match pst_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    pst3.Pulse_Prover_Common.pg
                                                                    FStar_Pervasives_Native.None
                                                                    "cannot match a vprop")
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    pst4 ->
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst4))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                 uu___2)))
                                                  uu___1))) uu___1))) uu___1))))
        uu___1 uu___
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Typing_Env.env,
                 Pulse_Prover_Substs.ss_t, Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit)
                   Pulse_Prover_Common.continuation_elaborator)
                 FStar_Pervasives.dtuple5,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun uvs ->
          fun goals ->
            fun goals_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (127)) (Prims.of_int (59))
                         (Prims.of_int (127)) (Prims.of_int (67)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (127)) (Prims.of_int (70))
                         (Prims.of_int (164)) (Prims.of_int (103)))))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
                (fun uu___ ->
                   (fun ctxt_frame_typing ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (129)) (Prims.of_int (4))
                                    (Prims.of_int (133)) (Prims.of_int (10)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (136)) (Prims.of_int (59))
                                    (Prims.of_int (164)) (Prims.of_int (103)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 {
                                   Pulse_Prover_Common.g0 = g;
                                   Pulse_Prover_Common.ctxt = ctxt;
                                   Pulse_Prover_Common.frame =
                                     Pulse_Syntax_Base.tm_emp;
                                   Pulse_Prover_Common.ctxt_frame_typing = ();
                                   Pulse_Prover_Common.goals = goals
                                 }))
                           (fun uu___ ->
                              (fun preamble ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (138))
                                               (Prims.of_int (4))
                                               (Prims.of_int (147))
                                               (Prims.of_int (25)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (148))
                                               (Prims.of_int (6))
                                               (Prims.of_int (164))
                                               (Prims.of_int (103)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            {
                                              Pulse_Prover_Common.pg = g;
                                              Pulse_Prover_Common.remaining_ctxt
                                                =
                                                (Pulse_Checker_VPropEquiv.vprop_as_list
                                                   ctxt);
                                              Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                = ();
                                              Pulse_Prover_Common.uvs = uvs;
                                              Pulse_Prover_Common.ss =
                                                Pulse_Prover_Substs.empty;
                                              Pulse_Prover_Common.solved =
                                                Pulse_Syntax_Base.tm_emp;
                                              Pulse_Prover_Common.unsolved =
                                                (Pulse_Checker_VPropEquiv.vprop_as_list
                                                   goals);
                                              Pulse_Prover_Common.solved_typing
                                                = ();
                                              Pulse_Prover_Common.k =
                                                (Pulse_Prover_Common.k_elab_equiv
                                                   g g ctxt
                                                   (Pulse_Prover_Common.op_Star
                                                      preamble.Pulse_Prover_Common.ctxt
                                                      preamble.Pulse_Prover_Common.frame)
                                                   ctxt
                                                   (Pulse_Prover_Common.op_Star
                                                      (Pulse_Prover_Common.op_Star
                                                         (Pulse_Checker_VPropEquiv.list_as_vprop
                                                            (Pulse_Checker_VPropEquiv.vprop_as_list
                                                               ctxt))
                                                         preamble.Pulse_Prover_Common.frame)
                                                      (Pulse_Prover_Common.op_Array_Access
                                                         Pulse_Prover_Substs.empty
                                                         Pulse_Syntax_Base.tm_emp))
                                                   (Pulse_Prover_Common.k_elab_unit
                                                      g ctxt) () ());
                                              Pulse_Prover_Common.goals_inv =
                                                ()
                                            }))
                                      (fun uu___ ->
                                         (fun pst ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.fst"
                                                          (Prims.of_int (149))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (149))
                                                          (Prims.of_int (22)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.fst"
                                                          (Prims.of_int (149))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (164))
                                                          (Prims.of_int (103)))))
                                                 (Obj.magic
                                                    (prover preamble pst))
                                                 (fun uu___ ->
                                                    (fun pst1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (53)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (103)))))
                                                            (Obj.magic
                                                               (Pulse_Prover_Substs.ss_to_nt_substs
                                                                  pst1.Pulse_Prover_Common.pg
                                                                  pst1.Pulse_Prover_Common.uvs
                                                                  pst1.Pulse_Prover_Common.ss))
                                                            (fun uu___ ->
                                                               (fun ropt ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (103)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    ropt
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst1.Pulse_Prover_Common.pg
                                                                    FStar_Pervasives_Native.None
                                                                    "prove: ss not well-typed"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nt ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    ((pst1.Pulse_Prover_Common.pg),
                                                                    (pst1.Pulse_Prover_Common.uvs),
                                                                    (pst1.Pulse_Prover_Common.ss),
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst1.Pulse_Prover_Common.remaining_ctxt),
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    g
                                                                    pst1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    ctxt
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    ctxt
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst1.Pulse_Prover_Common.remaining_ctxt)
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst1.Pulse_Prover_Common.ss
                                                                    pst1.Pulse_Prover_Common.solved))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst1.Pulse_Prover_Common.ss
                                                                    goals)
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst1.Pulse_Prover_Common.remaining_ctxt))
                                                                    pst1.Pulse_Prover_Common.k
                                                                    () ()))))))
                                                                 uu___)))
                                                      uu___))) uu___))) uu___)))
                     uu___)