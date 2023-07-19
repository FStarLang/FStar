open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (k_intro_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        (unit, unit) Pulse_Typing.prop_validity ->
          Pulse_Syntax_Base.vprop ->
            ((unit, unit, unit, unit)
               Pulse_Checker_Common.continuation_elaborator,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun d ->
        fun token ->
          fun frame ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.IntroPure.fst"
                       (Prims.of_int (23)) (Prims.of_int (10))
                       (Prims.of_int (23)) (Prims.of_int (63)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.IntroPure.fst"
                       (Prims.of_int (23)) (Prims.of_int (66))
                       (Prims.of_int (56)) (Prims.of_int (30)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Typing.wr
                      (Pulse_Syntax_Base.Tm_IntroPure
                         {
                           Pulse_Syntax_Base.p = p;
                           Pulse_Syntax_Base.should_check =
                             Pulse_Syntax_Base.should_check_true
                         })))
              (fun uu___ ->
                 (fun t ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Prover.IntroPure.fst"
                                  (Prims.of_int (24)) (Prims.of_int (10))
                                  (Prims.of_int (24)) (Prims.of_int (27)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Prover.IntroPure.fst"
                                  (Prims.of_int (24)) (Prims.of_int (30))
                                  (Prims.of_int (56)) (Prims.of_int (30)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> Pulse_Typing.comp_intro_pure p))
                         (fun uu___ ->
                            (fun c ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.IntroPure.fst"
                                             (Prims.of_int (25))
                                             (Prims.of_int (28))
                                             (Prims.of_int (25))
                                             (Prims.of_int (51)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.IntroPure.fst"
                                             (Prims.of_int (25))
                                             (Prims.of_int (54))
                                             (Prims.of_int (56))
                                             (Prims.of_int (30)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          Pulse_Typing.T_IntroPure
                                            (g, p, (), token)))
                                    (fun uu___ ->
                                       (fun d1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Prover.IntroPure.fst"
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (17)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Prover.IntroPure.fst"
                                                        (Prims.of_int (30))
                                                        (Prims.of_int (30))
                                                        (Prims.of_int (56))
                                                        (Prims.of_int (30)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ ->
                                                     Pulse_Typing_Env.fresh g))
                                               (fun uu___ ->
                                                  (fun x ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Prover.IntroPure.fst"
                                                                   (Prims.of_int (35))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (35))
                                                                   (Prims.of_int (58)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Prover.IntroPure.fst"
                                                                   (Prims.of_int (42))
                                                                   (Prims.of_int (20))
                                                                   (Prims.of_int (56))
                                                                   (Prims.of_int (30)))))
                                                          (Obj.magic
                                                             (Pulse_Checker_Common.continuation_elaborator_with_bind
                                                                g frame c t
                                                                d1 () x))
                                                          (fun k ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___ ->
                                                                  fun
                                                                    post_hint
                                                                    ->
                                                                    fun r ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    r))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d11) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    d11))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    empty_env
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Prover_Common.st_typing_weakening
                                                                    g
                                                                    empty_env
                                                                    t1 c1 d12
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    Pulse_Typing.tm_unit)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d13
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.k_elab_equiv
                                                                    g
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    Pulse_Typing.tm_unit)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    frame
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    frame
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    p) frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    p)) k ()
                                                                    ()
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d13))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___1)))))
                                                    uu___))) uu___))) uu___)))
                   uu___)
let (intro_pure :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.vprop Prims.list ->
          unit ->
            (unit Pulse_Prover_Common.prover_state
               FStar_Pervasives_Native.option,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun t ->
        fun unsolved' ->
          fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.IntroPure.fst"
                       (Prims.of_int (64)) (Prims.of_int (13))
                       (Prims.of_int (64)) (Prims.of_int (23)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.IntroPure.fst"
                       (Prims.of_int (64)) (Prims.of_int (26))
                       (Prims.of_int (151)) (Prims.of_int (14)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Pulse_Prover_Common.op_Array_Access
                      pst.Pulse_Prover_Common.ss t))
              (fun uu___1 ->
                 (fun t_ss ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Prover.IntroPure.fst"
                                  (Prims.of_int (69)) (Prims.of_int (10))
                                  (Prims.of_int (69)) (Prims.of_int (64)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Prover.IntroPure.fst"
                                  (Prims.of_int (69)) (Prims.of_int (67))
                                  (Prims.of_int (151)) (Prims.of_int (14)))))
                         (Obj.magic
                            (Pulse_Checker_Pure.core_check_term_with_expected_type
                               pst.Pulse_Prover_Common.pg t_ss
                               Pulse_Typing.tm_prop))
                         (fun uu___1 ->
                            (fun d ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.IntroPure.fst"
                                             (Prims.of_int (70))
                                             (Prims.of_int (16))
                                             (Prims.of_int (70))
                                             (Prims.of_int (53)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.IntroPure.fst"
                                             (Prims.of_int (70))
                                             (Prims.of_int (56))
                                             (Prims.of_int (151))
                                             (Prims.of_int (14)))))
                                    (Obj.magic
                                       (Pulse_Checker_Pure.check_prop_validity
                                          pst.Pulse_Prover_Common.pg t_ss ()))
                                    (fun uu___1 ->
                                       (fun d_valid ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Prover.IntroPure.fst"
                                                        (Prims.of_int (72))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (72))
                                                        (Prims.of_int (41)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Prover.IntroPure.fst"
                                                        (Prims.of_int (72))
                                                        (Prims.of_int (44))
                                                        (Prims.of_int (151))
                                                        (Prims.of_int (14)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Pulse_Typing_Env.fresh
                                                       (Pulse_Typing_Env.push_env
                                                          pst.Pulse_Prover_Common.pg
                                                          pst.Pulse_Prover_Common.uvs)))
                                               (fun uu___1 ->
                                                  (fun x ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Prover.IntroPure.fst"
                                                                   (Prims.of_int (74))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (74))
                                                                   (Prims.of_int (43)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Prover.IntroPure.fst"
                                                                   (Prims.of_int (74))
                                                                   (Prims.of_int (46))
                                                                   (Prims.of_int (151))
                                                                   (Prims.of_int (14)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                Pulse_Prover_Common.op_Star
                                                                  (Pulse_Syntax_Base.tm_pure
                                                                    t)
                                                                  pst.Pulse_Prover_Common.solved))
                                                          (fun uu___1 ->
                                                             (fun solved_new
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    unsolved'))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    unsolved_new
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    frame ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroPure.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (k_intro_pure
                                                                    pst.Pulse_Prover_Common.pg
                                                                    t_ss ()
                                                                    d_valid
                                                                    frame))
                                                                    (fun
                                                                    k_pure ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Checker_Common.k_elab_trans
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__pg
                                                                    preamble
                                                                    pst)
                                                                    pst.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__remaining_ctxt
                                                                    preamble
                                                                    pst))
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__ss
                                                                    preamble
                                                                    pst)
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__solved
                                                                    preamble
                                                                    pst)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    solved_new))
                                                                    pst.Pulse_Prover_Common.k
                                                                    (Pulse_Checker_Common.k_elab_equiv
                                                                    pst.Pulse_Prover_Common.pg
                                                                    pst.Pulse_Prover_Common.pg
                                                                    frame
                                                                    frame
                                                                    (Pulse_Prover_Common.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    t_ss))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    t_ss)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)))
                                                                    k_pure ()
                                                                    ())))))
                                                                    uu___1)))
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Prover_Common.pg
                                                                    =
                                                                    (pst.Pulse_Prover_Common.pg);
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (pst.Pulse_Prover_Common.remaining_ctxt);
                                                                    Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.uvs
                                                                    =
                                                                    (pst.Pulse_Prover_Common.uvs);
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (pst.Pulse_Prover_Common.ss);
                                                                    Pulse_Prover_Common.solved
                                                                    =
                                                                    solved_new;
                                                                    Pulse_Prover_Common.unsolved
                                                                    =
                                                                    unsolved_new;
                                                                    Pulse_Prover_Common.k
                                                                    = k;
                                                                    Pulse_Prover_Common.goals_inv
                                                                    = ();
                                                                    Pulse_Prover_Common.solved_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___1)))
                                                               uu___1)))
                                                    uu___1))) uu___1)))
                              uu___1))) uu___1)