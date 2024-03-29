open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (elim_exists_and_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
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
                (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                   (Prims.of_int (49)) (Prims.of_int (32))
                   (Prims.of_int (49)) (Prims.of_int (66)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                   (Prims.of_int (47)) (Prims.of_int (53))
                   (Prims.of_int (51)) (Prims.of_int (41)))))
          (Obj.magic (Pulse_Checker_Prover_ElimExists.elim_exists g ctxt ()))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Pervasives.Mkdtuple4 (g1, ctxt1, d1, k1) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (50)) (Prims.of_int (32))
                                  (Prims.of_int (50)) (Prims.of_int (53)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (49)) (Prims.of_int (69))
                                  (Prims.of_int (51)) (Prims.of_int (41)))))
                         (Obj.magic
                            (Pulse_Checker_Prover_ElimPure.elim_pure g1 ctxt1
                               ()))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 match uu___1 with
                                 | FStar_Pervasives.Mkdtuple4
                                     (g2, ctxt2, d2, k2) ->
                                     FStar_Pervasives.Mkdtuple4
                                       (g2, ctxt2, (),
                                         (Pulse_Checker_Base.k_elab_trans g
                                            g1 g2 ctxt ctxt1 ctxt2 k1 k2))))))
               uu___)
let (unsolved_equiv_pst :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop Prims.list ->
        unit -> unit Pulse_Checker_Prover_Base.prover_state)
  =
  fun preamble ->
    fun pst ->
      fun unsolved' ->
        fun d ->
          {
            Pulse_Checker_Prover_Base.pg = (pst.Pulse_Checker_Prover_Base.pg);
            Pulse_Checker_Prover_Base.remaining_ctxt =
              (pst.Pulse_Checker_Prover_Base.remaining_ctxt);
            Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing = ();
            Pulse_Checker_Prover_Base.uvs =
              (pst.Pulse_Checker_Prover_Base.uvs);
            Pulse_Checker_Prover_Base.ss = (pst.Pulse_Checker_Prover_Base.ss);
            Pulse_Checker_Prover_Base.nts =
              (pst.Pulse_Checker_Prover_Base.nts);
            Pulse_Checker_Prover_Base.solved =
              (pst.Pulse_Checker_Prover_Base.solved);
            Pulse_Checker_Prover_Base.unsolved = unsolved';
            Pulse_Checker_Prover_Base.k = (pst.Pulse_Checker_Prover_Base.k);
            Pulse_Checker_Prover_Base.goals_inv = ();
            Pulse_Checker_Prover_Base.solved_inv = ()
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
               (match Pulse_Syntax_Pure.inspect_term hd with
                | Pulse_Syntax_Pure.Tm_ExistsSL (uu___2, uu___3, uu___4) ->
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
               (match Pulse_Syntax_Pure.inspect_term hd with
                | Pulse_Syntax_Pure.Tm_Pure uu___2 ->
                    FStar_Pervasives.Mkdtuple3 ((hd :: pures), rest, ())
                | uu___2 ->
                    FStar_Pervasives.Mkdtuple3 (pures, (hd :: rest), ())))
let rec (prove_pures :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun preamble ->
         fun pst ->
           match pst.Pulse_Checker_Prover_Base.unsolved with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> pst)))
           | p::unsolved' ->
               Obj.magic
                 (Obj.repr
                    (match Pulse_Syntax_Pure.inspect_term p with
                     | Pulse_Syntax_Pure.Tm_Pure p1 ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (94)) (Prims.of_int (20))
                                    (Prims.of_int (94)) (Prims.of_int (59)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (95)) (Prims.of_int (6))
                                    (Prims.of_int (107)) (Prims.of_int (14)))))
                           (Obj.magic
                              (Pulse_Checker_Prover_IntroPure.intro_pure
                                 preamble pst p1 unsolved' ()))
                           (fun uu___ ->
                              (fun pst_opt ->
                                 match pst_opt with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (98))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (101))
                                                   (Prims.of_int (10)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (98))
                                                   (Prims.of_int (9))
                                                   (Prims.of_int (101))
                                                   (Prims.of_int (10)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (99))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (100))
                                                         (Prims.of_int (17)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (98))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (101))
                                                         (Prims.of_int (10)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.fst"
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (17)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.fst"
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (11))
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic
                                                         (Pulse_PP.pp
                                                            Pulse_PP.printable_fstar_term
                                                            p1))
                                                      (fun uu___ ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___1 ->
                                                              FStar_Pprint.op_Hat_Slash_Hat
                                                                (Pulse_PP.text
                                                                   "Cannot prove pure proposition")
                                                                uu___))))
                                                (fun uu___ ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 -> [uu___]))))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                Obj.magic
                                                  (Pulse_Typing_Env.fail_doc
                                                     pst.Pulse_Checker_Prover_Base.pg
                                                     FStar_Pervasives_Native.None
                                                     uu___)) uu___))
                                 | FStar_Pervasives_Native.Some pst1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (17)))))
                                          (Obj.magic
                                             (prove_pures preamble pst1))
                                          (fun pst2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___ -> pst2)))) uu___)
                     | uu___ ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (110)) (Prims.of_int (8))
                                    (Prims.of_int (111)) (Prims.of_int (50)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (109)) (Prims.of_int (6))
                                    (Prims.of_int (111)) (Prims.of_int (50)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.fst"
                                          (Prims.of_int (111))
                                          (Prims.of_int (11))
                                          (Prims.of_int (111))
                                          (Prims.of_int (49)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (590))
                                          (Prims.of_int (19))
                                          (Prims.of_int (590))
                                          (Prims.of_int (31)))))
                                 (Obj.magic
                                    (Pulse_Syntax_Printer.term_to_string
                                       (FStar_List_Tot_Base.hd
                                          pst.Pulse_Checker_Prover_Base.unsolved)))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         Prims.strcat
                                           "Impossible! prover.prove_pures: "
                                           (Prims.strcat uu___1
                                              " is not a pure, please file a bug-report")))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (Pulse_Typing_Env.fail
                                      pst.Pulse_Checker_Prover_Base.pg
                                      FStar_Pervasives_Native.None uu___1))
                                uu___1)))) uu___1 uu___
let rec (prover :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (120)) (Prims.of_int (2)) (Prims.of_int (123))
                 (Prims.of_int (55)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (125)) (Prims.of_int (2)) (Prims.of_int (185))
                 (Prims.of_int (36)))))
        (Obj.magic
           (Pulse_Checker_Prover_Util.debug_prover
              pst0.Pulse_Checker_Prover_Base.pg
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (123)) (Prims.of_int (6))
                            (Prims.of_int (123)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (121)) (Prims.of_int (4))
                            (Prims.of_int (123)) (Prims.of_int (54)))))
                   (Obj.magic
                      (Pulse_Syntax_Printer.term_to_string
                         (Pulse_Typing_Combinators.list_as_vprop
                            pst0.Pulse_Checker_Prover_Base.unsolved)))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (121))
                                       (Prims.of_int (4))
                                       (Prims.of_int (123))
                                       (Prims.of_int (54)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (121))
                                       (Prims.of_int (4))
                                       (Prims.of_int (123))
                                       (Prims.of_int (54)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (122))
                                             (Prims.of_int (6))
                                             (Prims.of_int (122))
                                             (Prims.of_int (60)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Printf.fst"
                                             (Prims.of_int (122))
                                             (Prims.of_int (8))
                                             (Prims.of_int (124))
                                             (Prims.of_int (44)))))
                                    (Obj.magic
                                       (Pulse_Syntax_Printer.term_to_string
                                          (Pulse_Typing_Combinators.list_as_vprop
                                             pst0.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            fun x ->
                                              Prims.strcat
                                                (Prims.strcat
                                                   "At the prover top-level with remaining_ctxt: "
                                                   (Prims.strcat uu___2
                                                      "\nunsolved: "))
                                                (Prims.strcat x "")))))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> uu___2 uu___1)))) uu___1))))
        (fun uu___ ->
           (fun uu___ ->
              match pst0.Pulse_Checker_Prover_Base.unsolved with
              | [] ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> pst0)))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.fst"
                                   (Prims.of_int (128)) (Prims.of_int (14))
                                   (Prims.of_int (128)) (Prims.of_int (45)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.fst"
                                   (Prims.of_int (130)) (Prims.of_int (4))
                                   (Prims.of_int (185)) (Prims.of_int (36)))))
                          (Obj.magic
                             (Pulse_Checker_Prover_ElimExists.elim_exists_pst
                                preamble pst0))
                          (fun uu___2 ->
                             (fun pst ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.fst"
                                              (Prims.of_int (130))
                                              (Prims.of_int (4))
                                              (Prims.of_int (132))
                                              (Prims.of_int (62)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.fst"
                                              (Prims.of_int (132))
                                              (Prims.of_int (63))
                                              (Prims.of_int (185))
                                              (Prims.of_int (36)))))
                                     (Obj.magic
                                        (Pulse_Checker_Prover_Util.debug_prover
                                           pst.Pulse_Checker_Prover_Base.pg
                                           (fun uu___2 ->
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (132))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (132))
                                                         (Prims.of_int (61)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (Pulse_Syntax_Printer.term_to_string
                                                      (Pulse_Typing_Combinators.list_as_vprop
                                                         pst.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        Prims.strcat
                                                          "prover: remaining_ctxt after elim exists: "
                                                          (Prims.strcat
                                                             uu___3 "\n"))))))
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (134))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (134))
                                                         (Prims.of_int (40)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (136))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (185))
                                                         (Prims.of_int (36)))))
                                                (Obj.magic
                                                   (Pulse_Checker_Prover_ElimPure.elim_pure_pst
                                                      preamble pst))
                                                (fun uu___3 ->
                                                   (fun pst1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (62)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                           (Obj.magic
                                                              (Pulse_Checker_Prover_Util.debug_prover
                                                                 pst1.Pulse_Checker_Prover_Base.pg
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst1.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "prover: remaining_ctxt after elim pure: "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n"))))))
                                                           (fun uu___3 ->
                                                              (fun uu___3 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    collect_exists
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst1.Pulse_Checker_Prover_Base.pg
                                                                    pst1.Pulse_Checker_Prover_Base.uvs)
                                                                    pst1.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (exs,
                                                                    rest, d)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst1.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    rest)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    exs)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover: tried to pull exists: exs: "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    " and rest: "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    unsolved_equiv_pst
                                                                    preamble
                                                                    pst1
                                                                    (FStar_List_Tot_Base.op_At
                                                                    exs rest)
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun pst2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst2.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst2.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "prover: unsolved after pulling exists at the top: "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match 
                                                                    pst2.Pulse_Checker_Prover_Base.unsolved
                                                                    with
                                                                    | 
                                                                    hd::unsolved'
                                                                    ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    hd
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_ExistsSL
                                                                    (u, b,
                                                                    body) ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover_IntroExists.intro_exists
                                                                    preamble
                                                                    pst2 u b
                                                                    body
                                                                    unsolved'
                                                                    () prover)
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    collect_pures
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst2.Pulse_Checker_Prover_Base.pg
                                                                    pst2.Pulse_Checker_Prover_Base.uvs)
                                                                    pst2.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
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
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    unsolved_equiv_pst
                                                                    preamble
                                                                    pst2
                                                                    (FStar_List_Tot_Base.op_At
                                                                    rest1
                                                                    pures) ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun pst3
                                                                    ->
                                                                    match 
                                                                    pst3.Pulse_Checker_Prover_Base.unsolved
                                                                    with
                                                                    | 
                                                                    q::tl ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    q
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_Pure
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (prove_pures
                                                                    preamble
                                                                    pst3)
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Match.match_q
                                                                    preamble
                                                                    pst3 q tl
                                                                    () prover))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    pst_opt
                                                                    ->
                                                                    match pst_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    q))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Cannot prove:")
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst3.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "In the context:")
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    [uu___11]))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___10
                                                                    ::
                                                                    uu___11))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Config.debug_flag
                                                                    "initial_solver_state"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    if
                                                                    uu___11
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    preamble.Pulse_Checker_Prover_Base.goals))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "The prover was started with goal:")
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "and initial context:")
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    [uu___13]))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___12
                                                                    ::
                                                                    uu___13))))
                                                                    uu___12)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> []))))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___10
                                                                    uu___11))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    pst3.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    msg))
                                                                    uu___10))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    pst4 ->
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst4))
                                                                    uu___10))))
                                                                    uu___9)))
                                                                    uu___8))))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                uu___3)))
                                                     uu___3))) uu___2)))
                               uu___2)))) uu___)
let rec (get_q_at_hd :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      Pulse_Syntax_Base.vprop ->
        (Pulse_Syntax_Base.vprop Prims.list, unit) Prims.dtuple2)
  =
  fun g ->
    fun l ->
      fun q ->
        match l with
        | hd::tl ->
            if Pulse_Syntax_Base.eq_tm hd q
            then Prims.Mkdtuple2 (tl, ())
            else
              (let uu___1 = get_q_at_hd g tl q in
               match uu___1 with
               | Prims.Mkdtuple2 (tl', uu___2) ->
                   Prims.Mkdtuple2 ((hd :: tl'), ()))
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Checker_Prover_Substs.nt_substs,
                 FStar_TypeChecker_Core.tot_or_ghost Prims.list,
                 Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit)
                   Pulse_Checker_Base.continuation_elaborator)
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
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (210)) (Prims.of_int (2))
                         (Prims.of_int (212)) (Prims.of_int (55)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (212)) (Prims.of_int (56))
                         (Prims.of_int (288)) (Prims.of_int (126)))))
                (Obj.magic
                   (Pulse_Checker_Prover_Util.debug_prover g
                      (fun uu___ ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (212)) (Prims.of_int (30))
                                    (Prims.of_int (212)) (Prims.of_int (54)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (211)) (Prims.of_int (4))
                                    (Prims.of_int (212)) (Prims.of_int (54)))))
                           (Obj.magic
                              (Pulse_Syntax_Printer.term_to_string goals))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.fst"
                                               (Prims.of_int (211))
                                               (Prims.of_int (4))
                                               (Prims.of_int (212))
                                               (Prims.of_int (54)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.fst"
                                               (Prims.of_int (211))
                                               (Prims.of_int (4))
                                               (Prims.of_int (212))
                                               (Prims.of_int (54)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.fst"
                                                     (Prims.of_int (212))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (212))
                                                     (Prims.of_int (29)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Printf.fst"
                                                     (Prims.of_int (122))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (124))
                                                     (Prims.of_int (44)))))
                                            (Obj.magic
                                               (Pulse_Syntax_Printer.term_to_string
                                                  ctxt))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    fun x ->
                                                      Prims.strcat
                                                        (Prims.strcat
                                                           "\nEnter top-level prove with ctxt: "
                                                           (Prims.strcat
                                                              uu___2
                                                              "\ngoals: "))
                                                        (Prims.strcat x "\n")))))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (214)) (Prims.of_int (15))
                                    (Prims.of_int (214)) (Prims.of_int (33)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (229)) (Prims.of_int (75))
                                    (Prims.of_int (288)) (Prims.of_int (126)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Typing_Combinators.vprop_as_list ctxt))
                           (fun uu___1 ->
                              (fun ctxt_l ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.fst"
                                               (Prims.of_int (231))
                                               (Prims.of_int (6))
                                               (Prims.of_int (235))
                                               (Prims.of_int (12)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.fst"
                                               (Prims.of_int (238))
                                               (Prims.of_int (43))
                                               (Prims.of_int (288))
                                               (Prims.of_int (126)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            {
                                              Pulse_Checker_Prover_Base.g0 =
                                                g;
                                              Pulse_Checker_Prover_Base.ctxt
                                                = ctxt;
                                              Pulse_Checker_Prover_Base.frame
                                                = Pulse_Syntax_Pure.tm_emp;
                                              Pulse_Checker_Prover_Base.ctxt_frame_typing
                                                = ();
                                              Pulse_Checker_Prover_Base.goals
                                                = goals
                                            }))
                                      (fun uu___1 ->
                                         (fun preamble ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.fst"
                                                          (Prims.of_int (240))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (250))
                                                          (Prims.of_int (21)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.fst"
                                                          (Prims.of_int (251))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (288))
                                                          (Prims.of_int (126)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       {
                                                         Pulse_Checker_Prover_Base.pg
                                                           = g;
                                                         Pulse_Checker_Prover_Base.remaining_ctxt
                                                           =
                                                           (Pulse_Typing_Combinators.vprop_as_list
                                                              ctxt);
                                                         Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                           = ();
                                                         Pulse_Checker_Prover_Base.uvs
                                                           = uvs;
                                                         Pulse_Checker_Prover_Base.ss
                                                           =
                                                           Pulse_Checker_Prover_Substs.empty;
                                                         Pulse_Checker_Prover_Base.nts
                                                           =
                                                           FStar_Pervasives_Native.None;
                                                         Pulse_Checker_Prover_Base.solved
                                                           =
                                                           Pulse_Syntax_Pure.tm_emp;
                                                         Pulse_Checker_Prover_Base.unsolved
                                                           =
                                                           (Pulse_Typing_Combinators.vprop_as_list
                                                              goals);
                                                         Pulse_Checker_Prover_Base.k
                                                           =
                                                           (Pulse_Checker_Base.k_elab_equiv
                                                              g g ctxt
                                                              (Pulse_Checker_Prover_Base.op_Star
                                                                 preamble.Pulse_Checker_Prover_Base.ctxt
                                                                 preamble.Pulse_Checker_Prover_Base.frame)
                                                              ctxt
                                                              (Pulse_Checker_Prover_Base.op_Star
                                                                 (Pulse_Checker_Prover_Base.op_Star
                                                                    (
                                                                    Pulse_Typing_Combinators.list_as_vprop
                                                                    (Pulse_Typing_Combinators.vprop_as_list
                                                                    ctxt))
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                 (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    Pulse_Checker_Prover_Substs.empty
                                                                    Pulse_Syntax_Pure.tm_emp))
                                                              (Pulse_Checker_Base.k_elab_unit
                                                                 g ctxt) ()
                                                              ());
                                                         Pulse_Checker_Prover_Base.goals_inv
                                                           = ();
                                                         Pulse_Checker_Prover_Base.solved_inv
                                                           = ()
                                                       }))
                                                 (fun uu___1 ->
                                                    (fun pst0 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (25)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (126)))))
                                                            (Obj.magic
                                                               (prover
                                                                  preamble
                                                                  pst0))
                                                            (fun uu___1 ->
                                                               (fun pst ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (126)))))
                                                                    (match 
                                                                    pst.Pulse_Checker_Prover_Base.nts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nts ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    nts)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Substs.ss_to_nt_substs
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.uvs
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    msg ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    (Prims.strcat
                                                                    "prover error: ill-typed substitutions ("
                                                                    (Prims.strcat
                                                                    msg ")"))))
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    nts ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    nts))))
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (nts,
                                                                    effect_labels)
                                                                    ->
                                                                    (match 
                                                                    Pulse_Checker_Prover_Substs.well_typed_nt_substs_prefix
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.uvs
                                                                    nts
                                                                    effect_labels
                                                                    uvs
                                                                    with
                                                                    | 
                                                                    (nts_uvs,
                                                                    nts_uvs_effect_labels)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    ((pst.Pulse_Checker_Prover_Base.pg),
                                                                    nts_uvs,
                                                                    nts_uvs_effect_labels,
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt),
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    g
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    ctxt
                                                                    Pulse_Syntax_Pure.tm_emp)
                                                                    ctxt
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    Pulse_Syntax_Pure.tm_emp)
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    nts))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    goals
                                                                    nts_uvs)
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    () ())))))))
                                                                 uu___1)))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)
let (canon_post : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st) =
  fun c ->
    let canon_st_comp_post c1 =
      match Pulse_Syntax_Pure.inspect_term
              (Pulse_Elaborate_Pure.elab_term c1.Pulse_Syntax_Base.post)
      with
      | Pulse_Syntax_Pure.Tm_FStar uu___ -> c1
      | post_v ->
          {
            Pulse_Syntax_Base.u = (c1.Pulse_Syntax_Base.u);
            Pulse_Syntax_Base.res = (c1.Pulse_Syntax_Base.res);
            Pulse_Syntax_Base.pre = (c1.Pulse_Syntax_Base.pre);
            Pulse_Syntax_Base.post =
              (Pulse_Syntax_Pure.pack_term_view_wr post_v
                 (Pulse_RuntimeUtils.range_of_term c1.Pulse_Syntax_Base.post))
          } in
    match c with
    | Pulse_Syntax_Base.C_ST s ->
        Pulse_Syntax_Base.C_ST (canon_st_comp_post s)
    | Pulse_Syntax_Base.C_STAtomic (i, obs, s) ->
        Pulse_Syntax_Base.C_STAtomic (i, obs, (canon_st_comp_post s))
    | Pulse_Syntax_Base.C_STGhost s ->
        Pulse_Syntax_Base.C_STGhost (canon_st_comp_post s)
let (typing_canon :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun t -> fun c -> fun d -> d
let (try_frame_pre_uvs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
            (unit, unit, unit) Pulse_Typing.st_typing)
            FStar_Pervasives.dtuple3 ->
            Pulse_Syntax_Base.ppname ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun uvs ->
          fun d ->
            fun res_ppname ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (315)) (Prims.of_int (22))
                         (Prims.of_int (315)) (Prims.of_int (23)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (313)) (Prims.of_int (42))
                         (Prims.of_int (386)) (Prims.of_int (88)))))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> d))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Pervasives.Mkdtuple3 (t, c, d1) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.fst"
                                        (Prims.of_int (317))
                                        (Prims.of_int (10))
                                        (Prims.of_int (317))
                                        (Prims.of_int (48)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.fst"
                                        (Prims.of_int (317))
                                        (Prims.of_int (51))
                                        (Prims.of_int (386))
                                        (Prims.of_int (88)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     Pulse_Typing_Env.push_context g
                                       "try_frame_pre"
                                       t.Pulse_Syntax_Base.range1))
                               (fun uu___1 ->
                                  (fun g1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (320))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (320))
                                                   (Prims.of_int (59)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (317))
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (386))
                                                   (Prims.of_int (88)))))
                                          (Obj.magic
                                             (prove g1 ctxt () uvs
                                                (Pulse_Syntax_Base.comp_pre c)
                                                ()))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple5
                                                    (g11, nts, effect_labels,
                                                     remaining_ctxt, k_frame)
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.fst"
                                                                  (Prims.of_int (324))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (324))
                                                                  (Prims.of_int (49)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.fst"
                                                                  (Prims.of_int (326))
                                                                  (Prims.of_int (82))
                                                                  (Prims.of_int (386))
                                                                  (Prims.of_int (88)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               Pulse_Typing_Metatheory.st_typing_weakening
                                                                 g1 uvs t c
                                                                 d1 g11))
                                                         (fun uu___2 ->
                                                            (fun d2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (35)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Substs.nt_subst_st_term
                                                                    t nts))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Substs.nt_subst_comp
                                                                    c nts))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun c1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Substs.st_typing_nt_substs_derived
                                                                    g11 uvs t
                                                                    c d2 nts
                                                                    effect_labels))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    (x, x_t)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    x_t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover error: for term "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ", implicit solution "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " has ghost effect")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g11
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t1.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2)))
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    d3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    d3))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    canon_post
                                                                    c1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun c2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    typing_canon
                                                                    g11 t1 c1
                                                                    d3))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d4
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    coerce_eq
                                                                    k_frame
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    k_frame1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g11))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.comp_res
                                                                    c2))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g11 x
                                                                    res_ppname
                                                                    ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2)
                                                                    (res_ppname,
                                                                    x))
                                                                    remaining_ctxt))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    ctxt' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Metatheory.st_typing_weakening_standard
                                                                    g11 t1
                                                                    (canon_post
                                                                    c1) d4
                                                                    g11))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d5
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (104)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.continuation_elaborator_with_bind
                                                                    g11
                                                                    remaining_ctxt
                                                                    c2 t1 d5
                                                                    ()
                                                                    (res_ppname,
                                                                    x)))
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match 
                                                                    Pulse_Typing_Metatheory_Base.st_comp_typing_inversion_cofinite
                                                                    g11
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)
                                                                    (FStar_Pervasives_Native.fst
                                                                    (Pulse_Typing_Metatheory_Base.comp_typing_inversion
                                                                    g11 c2
                                                                    (Pulse_Typing_Metatheory_Base.st_typing_correctness
                                                                    g11 t1 c2
                                                                    d5)))
                                                                    with
                                                                    | 
                                                                    (comp_res_typing_in_g1,
                                                                    uu___3,
                                                                    f) ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g2,
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax_Base.comp_u
                                                                    c2), ty,
                                                                    ())),
                                                                    (Prims.Mkdtuple2
                                                                    (ctxt',
                                                                    ())),
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    g1 g11 g2
                                                                    ctxt
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c2)
                                                                    remaining_ctxt)
                                                                    ctxt'
                                                                    k_frame1
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    g11 g2
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    remaining_ctxt
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c2))
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c2)
                                                                    remaining_ctxt)
                                                                    ctxt'
                                                                    ctxt' k
                                                                    () ())))))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                              uu___2)))
                                               uu___1))) uu___1))) uu___)
let (try_frame_pre :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
          (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3
          ->
          Pulse_Syntax_Base.ppname ->
            ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun d ->
          fun res_ppname ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (395)) (Prims.of_int (12))
                       (Prims.of_int (395)) (Prims.of_int (32)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (397)) (Prims.of_int (2))
                       (Prims.of_int (397)) (Prims.of_int (48)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g)))
              (fun uu___ ->
                 (fun uvs ->
                    Obj.magic (try_frame_pre_uvs g ctxt () uvs d res_ppname))
                   uu___)
let (prove_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit, unit) Pulse_Checker_Base.checker_result_t ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.range ->
            ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun r ->
        fun post_hint ->
          fun rng ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (406)) (Prims.of_int (10))
                       (Prims.of_int (406)) (Prims.of_int (46)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (408)) (Prims.of_int (2))
                       (Prims.of_int (463)) (Prims.of_int (99)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Typing_Env.push_context g "prove_post_hint" rng))
              (fun uu___ ->
                 (fun g1 ->
                    match post_hint with
                    | FStar_Pervasives_Native.None ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> r)))
                    | FStar_Pervasives_Native.Some post_hint1 ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.fst"
                                         (Prims.of_int (411))
                                         (Prims.of_int (79))
                                         (Prims.of_int (411))
                                         (Prims.of_int (80)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.fst"
                                         (Prims.of_int (410))
                                         (Prims.of_int (21))
                                         (Prims.of_int (463))
                                         (Prims.of_int (99)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ -> r))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | FStar_Pervasives.Mkdtuple5
                                          (x, g2, FStar_Pervasives.Mkdtuple3
                                           (u_ty, ty, ty_typing),
                                           Prims.Mkdtuple2
                                           (ctxt', ctxt'_typing), k)
                                          ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (413))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (413))
                                                        (Prims.of_int (44)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (413))
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (463))
                                                        (Prims.of_int (99)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Pulse_Syntax_Base.mk_ppname_no_range
                                                       "_posth"))
                                               (fun uu___1 ->
                                                  (fun ppname ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.fst"
                                                                   (Prims.of_int (414))
                                                                   (Prims.of_int (27))
                                                                   (Prims.of_int (414))
                                                                   (Prims.of_int (66)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.fst"
                                                                   (Prims.of_int (417))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (463))
                                                                   (Prims.of_int (99)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                Pulse_Syntax_Naming.open_term_nv
                                                                  post_hint1.Pulse_Typing.post
                                                                  (ppname, x)))
                                                          (fun uu___1 ->
                                                             (fun
                                                                post_hint_opened
                                                                ->
                                                                if
                                                                  Prims.op_Negation
                                                                    (
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    post_hint1.Pulse_Typing.ret_ty)
                                                                then
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    ty))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_PP.indent
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    post_hint1.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_PP.indent
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "does not match the expected")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "The return type")
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    [uu___1]))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (Pulse_PP.text
                                                                    "Error in proving postcondition")
                                                                    :: uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                    uu___1))
                                                                    uu___1)))
                                                                else
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    post_hint_opened
                                                                    ctxt'
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g2,
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (u_ty,
                                                                    ty, ())),
                                                                    (Prims.Mkdtuple2
                                                                    (ctxt',
                                                                    ())), k)))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (prove g2
                                                                    ctxt' ()
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g2))
                                                                    post_hint_opened
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (g3, nts,
                                                                    uu___4,
                                                                    remaining_ctxt,
                                                                    k_post)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    coerce_eq
                                                                    k_post ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    k_post1
                                                                    ->
                                                                    match 
                                                                    Pulse_Checker_Base.check_equiv_emp
                                                                    g3
                                                                    remaining_ctxt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    remaining_ctxt))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_PP.indent
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Inferred postcondition additionally contains")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5;
                                                                    if
                                                                    Pulse_Syntax_Pure.uu___is_Tm_Star
                                                                    (Pulse_Syntax_Pure.inspect_term
                                                                    remaining_ctxt)
                                                                    then
                                                                    Pulse_PP.text
                                                                    "Did you forget to free these resources?"
                                                                    else
                                                                    Pulse_PP.text
                                                                    "Did you forget to free this resource?"]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (Pulse_PP.text
                                                                    "Error in proving postcondition")
                                                                    :: uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                    uu___5))
                                                                    uu___5)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g3,
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (u_ty,
                                                                    ty, ())),
                                                                    (Prims.Mkdtuple2
                                                                    (post_hint_opened,
                                                                    ())),
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    g g2 g3
                                                                    ctxt
                                                                    (FStar_Pervasives.dfst
                                                                    (Prims.Mkdtuple2
                                                                    (ctxt',
                                                                    ())))
                                                                    post_hint_opened
                                                                    k
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    g2 g3
                                                                    ctxt'
                                                                    ctxt'
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    post_hint_opened
                                                                    remaining_ctxt)
                                                                    post_hint_opened
                                                                    k_post1
                                                                    () ())))))))
                                                                    uu___5)))
                                                                    uu___3)))))
                                                               uu___1)))
                                                    uu___1))) uu___)))) uu___)