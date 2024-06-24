open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (check_equiv_emp' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      (unit FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           match Pulse_Checker_Base.check_equiv_emp g p with
           | FStar_Pervasives_Native.Some t ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.Some ())))
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                                (Prims.of_int (50)) (Prims.of_int (10))
                                (Prims.of_int (50)) (Prims.of_int (71)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                                (Prims.of_int (50)) (Prims.of_int (4))
                                (Prims.of_int (53)) (Prims.of_int (21)))))
                       (Obj.magic
                          (Pulse_Typing_Util.check_equiv_now_nosmt
                             (Pulse_Typing.elab_env g) p
                             Pulse_Syntax_Pure.tm_emp))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               match uu___ with
                               | (FStar_Pervasives_Native.Some tok, uu___2)
                                   -> FStar_Pervasives_Native.Some ()
                               | (FStar_Pervasives_Native.None, uu___2) ->
                                   FStar_Pervasives_Native.None))))) uu___1
        uu___
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
                   (Prims.of_int (62)) (Prims.of_int (32))
                   (Prims.of_int (62)) (Prims.of_int (66)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                   (Prims.of_int (60)) (Prims.of_int (53))
                   (Prims.of_int (64)) (Prims.of_int (41)))))
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
                                  (Prims.of_int (63)) (Prims.of_int (32))
                                  (Prims.of_int (63)) (Prims.of_int (53)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (62)) (Prims.of_int (69))
                                  (Prims.of_int (64)) (Prims.of_int (41)))))
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
            Pulse_Checker_Prover_Base.solved_inv = ();
            Pulse_Checker_Prover_Base.progress =
              (pst.Pulse_Checker_Prover_Base.progress);
            Pulse_Checker_Prover_Base.allow_ambiguous =
              (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
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
                                    (Prims.of_int (107)) (Prims.of_int (20))
                                    (Prims.of_int (107)) (Prims.of_int (59)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (108)) (Prims.of_int (6))
                                    (Prims.of_int (119)) (Prims.of_int (14)))))
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
                                                   (Prims.of_int (110))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (113))
                                                   (Prims.of_int (10)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (110))
                                                   (Prims.of_int (9))
                                                   (Prims.of_int (113))
                                                   (Prims.of_int (10)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (111))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (112))
                                                         (Prims.of_int (17)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (110))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (113))
                                                         (Prims.of_int (10)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.fst"
                                                               (Prims.of_int (112))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (112))
                                                               (Prims.of_int (17)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.fst"
                                                               (Prims.of_int (111))
                                                               (Prims.of_int (11))
                                                               (Prims.of_int (112))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic
                                                         (Pulse_PP.pp
                                                            Pulse_PP.printable_term
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
                                                   (Prims.of_int (115))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (115))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.fst"
                                                   (Prims.of_int (115))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (115))
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
                                    (Prims.of_int (122)) (Prims.of_int (8))
                                    (Prims.of_int (123)) (Prims.of_int (50)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (121)) (Prims.of_int (6))
                                    (Prims.of_int (123)) (Prims.of_int (50)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.fst"
                                          (Prims.of_int (123))
                                          (Prims.of_int (11))
                                          (Prims.of_int (123))
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
let (normalize_vprop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      ((Pulse_Syntax_Base.vprop, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun v ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (130)) (Prims.of_int (11))
                 (Prims.of_int (130)) (Prims.of_int (86)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (130)) (Prims.of_int (89))
                 (Prims.of_int (132)) (Prims.of_int (22)))))
        (Obj.magic
           (FStar_Tactics_V2_Builtins.norm_well_typed_term
              (Pulse_Typing.elab_env g)
              [FStar_Pervasives.unascribe;
              FStar_Pervasives.primops;
              FStar_Pervasives.iota] v))
        (fun v' ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Prims.Mkdtuple2 (v', ())))
let (normalize_vprop_context :
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
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (139)) (Prims.of_int (13))
                 (Prims.of_int (139)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (139)) (Prims.of_int (34))
                 (Prims.of_int (159)) (Prims.of_int (3)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> pst.Pulse_Checker_Prover_Base.remaining_ctxt))
        (fun uu___ ->
           (fun ctxt ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (140)) (Prims.of_int (14))
                            (Prims.of_int (140)) (Prims.of_int (119)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (140)) (Prims.of_int (122))
                            (Prims.of_int (159)) (Prims.of_int (3)))))
                   (Obj.magic
                      (FStar_Tactics_Util.map
                         (FStar_Tactics_V2_Builtins.norm_well_typed_term
                            (Pulse_Typing.elab_env
                               pst.Pulse_Checker_Prover_Base.pg)
                            [FStar_Pervasives.unascribe;
                            FStar_Pervasives.primops;
                            FStar_Pervasives.iota]) ctxt))
                   (fun uu___ ->
                      (fun ctxt' ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (142))
                                       (Prims.of_int (17))
                                       (Prims.of_int (142))
                                       (Prims.of_int (29)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (142))
                                       (Prims.of_int (32))
                                       (Prims.of_int (159))
                                       (Prims.of_int (3)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    pst.Pulse_Checker_Prover_Base.unsolved))
                              (fun uu___ ->
                                 (fun unsolved ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.fst"
                                                  (Prims.of_int (143))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (143))
                                                  (Prims.of_int (127)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.fst"
                                                  (Prims.of_int (145))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (159))
                                                  (Prims.of_int (3)))))
                                         (Obj.magic
                                            (FStar_Tactics_Util.map
                                               (FStar_Tactics_V2_Builtins.norm_well_typed_term
                                                  (Pulse_Typing.elab_env
                                                     pst.Pulse_Checker_Prover_Base.pg)
                                                  [FStar_Pervasives.unascribe;
                                                  FStar_Pervasives.primops;
                                                  FStar_Pervasives.iota])
                                               unsolved))
                                         (fun uu___ ->
                                            (fun unsolved' ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.fst"
                                                             (Prims.of_int (145))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (150))
                                                             (Prims.of_int (3)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.fst"
                                                             (Prims.of_int (152))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (158))
                                                             (Prims.of_int (30)))))
                                                    (if
                                                       Pulse_RuntimeUtils.debug_at_level
                                                         (Pulse_Typing_Env.fstar_env
                                                            pst.Pulse_Checker_Prover_Base.pg)
                                                         "ggg"
                                                     then
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    ctxt))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    ctxt'))
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
                                                                    uu___ ::
                                                                    uu___1))))
                                                                    uu___)))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    (Pulse_PP.text
                                                                    "PROVER Normalized context")
                                                                    :: uu___))))
                                                               (fun uu___ ->
                                                                  (fun uu___
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    uu___))
                                                                    uu___)))
                                                     else
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___1 ->
                                                                  ()))))
                                                    (fun uu___ ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            {
                                                              Pulse_Checker_Prover_Base.pg
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.pg);
                                                              Pulse_Checker_Prover_Base.remaining_ctxt
                                                                = ctxt';
                                                              Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                = ();
                                                              Pulse_Checker_Prover_Base.uvs
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.uvs);
                                                              Pulse_Checker_Prover_Base.ss
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.ss);
                                                              Pulse_Checker_Prover_Base.nts
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.nts);
                                                              Pulse_Checker_Prover_Base.solved
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.solved);
                                                              Pulse_Checker_Prover_Base.unsolved
                                                                = unsolved';
                                                              Pulse_Checker_Prover_Base.k
                                                                =
                                                                (Pulse_Checker_Base.k_elab_equiv
                                                                   preamble.Pulse_Checker_Prover_Base.g0
                                                                   (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__pg
                                                                    preamble
                                                                    pst)
                                                                   (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                   (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                   (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__remaining_ctxt
                                                                    preamble
                                                                    pst))
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__ss
                                                                    preamble
                                                                    pst)
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__solved
                                                                    preamble
                                                                    pst)))
                                                                   (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    ctxt')
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                   pst.Pulse_Checker_Prover_Base.k
                                                                   () ());
                                                              Pulse_Checker_Prover_Base.goals_inv
                                                                = ();
                                                              Pulse_Checker_Prover_Base.solved_inv
                                                                = ();
                                                              Pulse_Checker_Prover_Base.progress
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.progress);
                                                              Pulse_Checker_Prover_Base.allow_ambiguous
                                                                =
                                                                (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                            })))) uu___)))
                                   uu___))) uu___))) uu___)
let rec (__intro_any_exists :
  Prims.nat ->
    Pulse_Checker_Prover_Base.preamble ->
      unit Pulse_Checker_Prover_Base.prover_state ->
        Pulse_Checker_Prover_Base.prover_t ->
          (unit Pulse_Checker_Prover_Base.prover_state, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun n ->
             fun preamble ->
               fun pst ->
                 fun prover ->
                   if n = Prims.int_zero
                   then
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___ -> pst)))
                   else
                     Obj.magic
                       (Obj.repr
                          (match pst.Pulse_Checker_Prover_Base.unsolved with
                           | [] ->
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> pst))
                           | hd::unsolved' ->
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (176))
                                             (Prims.of_int (15))
                                             (Prims.of_int (176))
                                             (Prims.of_int (26)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (177))
                                             (Prims.of_int (6))
                                             (Prims.of_int (190))
                                             (Prims.of_int (43)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          Pulse_Checker_Prover_Base.op_Array_Access
                                            pst.Pulse_Checker_Prover_Base.ss
                                            hd))
                                    (fun uu___1 ->
                                       (fun hd1 ->
                                          match Pulse_Syntax_Pure.inspect_term
                                                  hd1
                                          with
                                          | Pulse_Syntax_Pure.Tm_ExistsSL
                                              (u, b, body) ->
                                              Obj.magic
                                                (Pulse_Checker_Prover_IntroExists.intro_exists
                                                   preamble pst u b body
                                                   unsolved' () prover)
                                          | uu___1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (186))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (188))
                                                            (Prims.of_int (30)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (190))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (190))
                                                            (Prims.of_int (43)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         {
                                                           Pulse_Checker_Prover_Base.pg
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.pg);
                                                           Pulse_Checker_Prover_Base.remaining_ctxt
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                           Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                             = ();
                                                           Pulse_Checker_Prover_Base.uvs
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.uvs);
                                                           Pulse_Checker_Prover_Base.ss
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.ss);
                                                           Pulse_Checker_Prover_Base.nts
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.nts);
                                                           Pulse_Checker_Prover_Base.solved
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.solved);
                                                           Pulse_Checker_Prover_Base.unsolved
                                                             =
                                                             (FStar_List_Tot_Base.op_At
                                                                unsolved'
                                                                [hd1]);
                                                           Pulse_Checker_Prover_Base.k
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.k);
                                                           Pulse_Checker_Prover_Base.goals_inv
                                                             = ();
                                                           Pulse_Checker_Prover_Base.solved_inv
                                                             = ();
                                                           Pulse_Checker_Prover_Base.progress
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.progress);
                                                           Pulse_Checker_Prover_Base.allow_ambiguous
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                         }))
                                                   (fun uu___2 ->
                                                      (fun pst1 ->
                                                         Obj.magic
                                                           (__intro_any_exists
                                                              (n -
                                                                 Prims.int_one)
                                                              preamble pst1
                                                              prover)) uu___2)))
                                         uu___1))))) uu___3 uu___2 uu___1
            uu___
let (intro_any_exists :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Checker_Prover_Base.prover_t ->
        (unit Pulse_Checker_Prover_Base.prover_state, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun prover ->
        __intro_any_exists
          (FStar_List_Tot_Base.length pst.Pulse_Checker_Prover_Base.unsolved)
          preamble pst prover
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
                 (Prims.of_int (206)) (Prims.of_int (2)) (Prims.of_int (210))
                 (Prims.of_int (34)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (210)) (Prims.of_int (35))
                 (Prims.of_int (344)) (Prims.of_int (38)))))
        (Obj.magic
           (Pulse_Checker_Prover_Util.debug_prover
              pst0.Pulse_Checker_Prover_Base.pg
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (210)) (Prims.of_int (6))
                            (Prims.of_int (210)) (Prims.of_int (33)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (207)) (Prims.of_int (4))
                            (Prims.of_int (210)) (Prims.of_int (33)))))
                   (Obj.magic
                      (Pulse_Show.show Pulse_Show.tac_showable_bool
                         pst0.Pulse_Checker_Prover_Base.allow_ambiguous))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (207))
                                       (Prims.of_int (4))
                                       (Prims.of_int (210))
                                       (Prims.of_int (33)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (207))
                                       (Prims.of_int (4))
                                       (Prims.of_int (210))
                                       (Prims.of_int (33)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (209))
                                             (Prims.of_int (6))
                                             (Prims.of_int (209))
                                             (Prims.of_int (42)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (207))
                                             (Prims.of_int (4))
                                             (Prims.of_int (210))
                                             (Prims.of_int (33)))))
                                    (Obj.magic
                                       (Pulse_Show.show
                                          Pulse_Show.tac_showable_r_term
                                          (Pulse_Syntax_Pure.list_as_vprop
                                             pst0.Pulse_Checker_Prover_Base.unsolved)))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (207))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (210))
                                                        (Prims.of_int (33)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (207))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (210))
                                                        (Prims.of_int (33)))))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.fst"
                                                              (Prims.of_int (208))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (208))
                                                              (Prims.of_int (48)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Printf.fst"
                                                              (Prims.of_int (122))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (124))
                                                              (Prims.of_int (44)))))
                                                     (Obj.magic
                                                        (Pulse_Show.show
                                                           Pulse_Show.tac_showable_r_term
                                                           (Pulse_Syntax_Pure.list_as_vprop
                                                              pst0.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             fun x ->
                                                               fun x1 ->
                                                                 Prims.strcat
                                                                   (Prims.strcat
                                                                    (Prims.strcat
                                                                    "At the prover top-level with remaining_ctxt: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n  unsolved: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n  allow_ambiguous: "))
                                                                   (Prims.strcat
                                                                    x1 "\n")))))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       uu___3 uu___2))))
                                         uu___2)))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> uu___2 uu___1)))) uu___1))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (212)) (Prims.of_int (12))
                            (Prims.of_int (212)) (Prims.of_int (16)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (212)) (Prims.of_int (19))
                            (Prims.of_int (344)) (Prims.of_int (38)))))
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> pst0))
                   (fun uu___1 ->
                      (fun pst ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (213))
                                       (Prims.of_int (14))
                                       (Prims.of_int (213))
                                       (Prims.of_int (39)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (214))
                                       (Prims.of_int (2))
                                       (Prims.of_int (344))
                                       (Prims.of_int (38)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    {
                                      Pulse_Checker_Prover_Base.pg =
                                        (pst.Pulse_Checker_Prover_Base.pg);
                                      Pulse_Checker_Prover_Base.remaining_ctxt
                                        =
                                        (pst.Pulse_Checker_Prover_Base.remaining_ctxt);
                                      Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                        = ();
                                      Pulse_Checker_Prover_Base.uvs =
                                        (pst.Pulse_Checker_Prover_Base.uvs);
                                      Pulse_Checker_Prover_Base.ss =
                                        (pst.Pulse_Checker_Prover_Base.ss);
                                      Pulse_Checker_Prover_Base.nts =
                                        (pst.Pulse_Checker_Prover_Base.nts);
                                      Pulse_Checker_Prover_Base.solved =
                                        (pst.Pulse_Checker_Prover_Base.solved);
                                      Pulse_Checker_Prover_Base.unsolved =
                                        (pst.Pulse_Checker_Prover_Base.unsolved);
                                      Pulse_Checker_Prover_Base.k =
                                        (pst.Pulse_Checker_Prover_Base.k);
                                      Pulse_Checker_Prover_Base.goals_inv =
                                        ();
                                      Pulse_Checker_Prover_Base.solved_inv =
                                        ();
                                      Pulse_Checker_Prover_Base.progress =
                                        false;
                                      Pulse_Checker_Prover_Base.allow_ambiguous
                                        =
                                        (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                    }))
                              (fun uu___1 ->
                                 (fun pst1 ->
                                    match pst1.Pulse_Checker_Prover_Base.unsolved
                                    with
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
                                                         (Prims.of_int (223))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (223))
                                                         (Prims.of_int (41)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (223))
                                                         (Prims.of_int (44))
                                                         (Prims.of_int (344))
                                                         (Prims.of_int (38)))))
                                                (Obj.magic
                                                   (normalize_vprop_context
                                                      preamble pst1))
                                                (fun uu___2 ->
                                                   (fun pst2 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (44)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                           (Obj.magic
                                                              (Pulse_Checker_Prover_ElimExists.elim_exists_pst
                                                                 preamble
                                                                 pst2))
                                                           (fun uu___2 ->
                                                              (fun pst3 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst3.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (229))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst3.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "prover: remaining_ctxt after elim exists: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if
                                                                    pst3.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst3)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_ElimPure.elim_pure_pst
                                                                    preamble
                                                                    pst3))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun pst4
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst4.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (238))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst4.Pulse_Checker_Prover_Base.remaining_ctxt)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "prover: remaining_ctxt after elim pure: "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if
                                                                    pst4.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst4)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    collect_exists
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst4.Pulse_Checker_Prover_Base.pg
                                                                    pst4.Pulse_Checker_Prover_Base.uvs)
                                                                    pst4.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
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
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst4.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    rest)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (245))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    exs)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover: tried to pull exists: exs: "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " and rest: "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    if
                                                                    pst4.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst4)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    unsolved_equiv_pst
                                                                    preamble
                                                                    pst4
                                                                    (FStar_List_Tot_Base.op_At
                                                                    exs rest)
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun pst5
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst5.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (252))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst5.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "prover: unsolved after pulling exists at the top: "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    if
                                                                    pst5.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst5)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Explode.explode
                                                                    preamble
                                                                    pst5))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun pst6
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst6.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst6.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst6.Pulse_Checker_Prover_Base.unsolved))))
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
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (55)))))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst6.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover: unsolved after exploding: "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    " /// ("))
                                                                    (Prims.strcat
                                                                    x ")\n")))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___13
                                                                    uu___12))))
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    if
                                                                    pst6.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst6)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Match.match_syntactic
                                                                    preamble
                                                                    pst6))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun pst7
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst7.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst7.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "prover: unsolved after syntactic match: "
                                                                    (Prims.strcat
                                                                    uu___14
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    pst7.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst7)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Match.match_fastunif
                                                                    preamble
                                                                    pst7))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun pst8
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst8.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst8.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    "prover: unsolved after fastunif: "
                                                                    (Prims.strcat
                                                                    uu___16
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    if
                                                                    pst8.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst8)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Match.match_fastunif_i
                                                                    preamble
                                                                    pst8))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun pst9
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst9.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst9.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    "prover: unsolved after fastunif_inst: "
                                                                    (Prims.strcat
                                                                    uu___18
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    if
                                                                    pst9.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst9)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Match.match_full
                                                                    preamble
                                                                    pst9))
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    pst10 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    pst10.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (293))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst10.Pulse_Checker_Prover_Base.unsolved)))
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    "prover: unsolved after full match: "
                                                                    (Prims.strcat
                                                                    uu___20
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    if
                                                                    pst10.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst10)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (intro_any_exists
                                                                    preamble
                                                                    pst10
                                                                    prover))
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    pst11 ->
                                                                    if
                                                                    pst11.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (prover
                                                                    preamble
                                                                    pst11))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    pst11.Pulse_Checker_Prover_Base.unsolved
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    -> pst11))
                                                                    | 
                                                                    hd::unsolved'
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    collect_pures
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst11.Pulse_Checker_Prover_Base.pg
                                                                    pst11.Pulse_Checker_Prover_Base.uvs)
                                                                    pst11.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    match uu___22
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
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    unsolved_equiv_pst
                                                                    preamble
                                                                    pst11
                                                                    (FStar_List_Tot_Base.op_At
                                                                    rest1
                                                                    pures) ()))
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    pst12 ->
                                                                    match 
                                                                    pst12.Pulse_Checker_Prover_Base.unsolved
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    -> pst12)))
                                                                    | 
                                                                    q::tl ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    q
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_Pure
                                                                    uu___23
                                                                    ->
                                                                    prove_pures
                                                                    preamble
                                                                    pst12
                                                                    | 
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.filter
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Pure.uu___is_Tm_Pure
                                                                    (Pulse_Syntax_Pure.inspect_term
                                                                    t)))))
                                                                    uu___24)
                                                                    pst12.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    non_pures
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun q1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst12.Pulse_Checker_Prover_Base.ss
                                                                    q1)))
                                                                    uu___24)
                                                                    non_pures))
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    non_pures1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst12.Pulse_Checker_Prover_Base.ss
                                                                    q))
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    q_norm ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (check_equiv_emp'
                                                                    pst12.Pulse_Checker_Prover_Base.pg
                                                                    q_norm))
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.uvs);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.ss);
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.nts);
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.solved);
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    =
                                                                    unsolved';
                                                                    Pulse_Checker_Prover_Base.k
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.k);
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.progress
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.progress);
                                                                    Pulse_Checker_Prover_Base.allow_ambiguous
                                                                    =
                                                                    (pst12.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                                    }))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun pst'
                                                                    ->
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst'))
                                                                    uu___25))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Pure.canon_vprop_list_print
                                                                    non_pures1))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    uu___25))
                                                                    uu___25)))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___25))))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Cannot prove:")
                                                                    uu___25))))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Pure.canon_vprop_list_print
                                                                    pst12.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    uu___26))
                                                                    uu___26)))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___26))))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "In the context:")
                                                                    uu___26))))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    [uu___26]))))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    uu___25
                                                                    ::
                                                                    uu___26))))
                                                                    uu___25)))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (Pulse_Config.debug_flag
                                                                    "initial_solver_state"))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    if
                                                                    uu___26
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    preamble.Pulse_Checker_Prover_Base.goals))
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___27))))
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "The prover was started with goal:")
                                                                    uu___27))))
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt))
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___28))))
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "and initial context:")
                                                                    uu___28))))
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    [uu___28]))))
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    uu___27
                                                                    ::
                                                                    uu___28))))
                                                                    uu___27)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    -> []))))
                                                                    uu___26)))
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___25
                                                                    uu___26))))
                                                                    uu___25)))
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    pst12.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    msg))
                                                                    uu___25)))
                                                                    uu___24)))
                                                                    uu___24)))
                                                                    uu___24)))
                                                                    uu___24))))
                                                                    uu___23)))
                                                                    uu___22)))))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___2)))
                                                                uu___2)))
                                                     uu___2)))) uu___1)))
                        uu___1))) uu___)
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
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.vprop ->
              unit ->
                ((Pulse_Typing_Env.env,
                   Pulse_Checker_Prover_Substs.nt_substs,
                   FStar_TypeChecker_Core.tot_or_ghost Prims.list,
                   Pulse_Syntax_Base.vprop,
                   (unit, unit, unit, unit)
                     Pulse_Checker_Base.continuation_elaborator)
                   FStar_Pervasives.dtuple5,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_ambiguous ->
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
                           (Prims.of_int (370)) (Prims.of_int (2))
                           (Prims.of_int (372)) (Prims.of_int (55)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                           (Prims.of_int (372)) (Prims.of_int (56))
                           (Prims.of_int (464)) (Prims.of_int (126)))))
                  (Obj.magic
                     (Pulse_Checker_Prover_Util.debug_prover g
                        (fun uu___ ->
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.fst"
                                      (Prims.of_int (372))
                                      (Prims.of_int (30))
                                      (Prims.of_int (372))
                                      (Prims.of_int (54)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.fst"
                                      (Prims.of_int (371)) (Prims.of_int (4))
                                      (Prims.of_int (372))
                                      (Prims.of_int (54)))))
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
                                                 (Prims.of_int (371))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (372))
                                                 (Prims.of_int (54)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (371))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (372))
                                                 (Prims.of_int (54)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.fst"
                                                       (Prims.of_int (372))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (372))
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
                                                          (Prims.strcat x
                                                             "\n")))))
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
                                      (Prims.of_int (374))
                                      (Prims.of_int (15))
                                      (Prims.of_int (374))
                                      (Prims.of_int (33)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.fst"
                                      (Prims.of_int (389))
                                      (Prims.of_int (75))
                                      (Prims.of_int (464))
                                      (Prims.of_int (126)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   Pulse_Syntax_Pure.vprop_as_list ctxt))
                             (fun uu___1 ->
                                (fun ctxt_l ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (391))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (395))
                                                 (Prims.of_int (12)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (398))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (464))
                                                 (Prims.of_int (126)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              {
                                                Pulse_Checker_Prover_Base.g0
                                                  = g;
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
                                                            (Prims.of_int (400))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (412))
                                                            (Prims.of_int (40)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (413))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (464))
                                                            (Prims.of_int (126)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Checker_Prover_Base.pg
                                                             = g;
                                                           Pulse_Checker_Prover_Base.remaining_ctxt
                                                             =
                                                             (Pulse_Syntax_Pure.vprop_as_list
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
                                                             (Pulse_Syntax_Pure.vprop_as_list
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    (Pulse_Syntax_Pure.vprop_as_list
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
                                                             = ();
                                                           Pulse_Checker_Prover_Base.progress
                                                             = false;
                                                           Pulse_Checker_Prover_Base.allow_ambiguous
                                                             =
                                                             allow_ambiguous
                                                         }))
                                                   (fun uu___1 ->
                                                      (fun pst0 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (25)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (126)))))
                                                              (Obj.magic
                                                                 (prover
                                                                    preamble
                                                                    pst0))
                                                              (fun uu___1 ->
                                                                 (fun pst ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (464))
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
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (445))
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_env
                                                                    pst.Pulse_Checker_Prover_Base.pg))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.pg =")
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
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_env
                                                                    pst.Pulse_Checker_Prover_Base.uvs))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.uvs =")
                                                                    uu___2))))
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
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_Checker_Prover_Substs.pp_ss_t
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.ss =")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.remaining_ctxt =")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.unsolved =")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___4 ::
                                                                    uu___5))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___3 ::
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___2 ::
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___1 ::
                                                                    uu___2))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (Pulse_PP.text
                                                                    (Prims.strcat
                                                                    "Prover error: ill-typed substitutions ("
                                                                    (Prims.strcat
                                                                    msg ")")))
                                                                    :: uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    uu___1))
                                                                    uu___1)))
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
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
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    Pulse_Syntax_Pure.tm_emp)
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    nts))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    goals
                                                                    nts_uvs)
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    () ())))))))
                                                                   uu___1)))
                                                        uu___1))) uu___1)))
                                  uu___1))) uu___)
let (canon_post : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st) =
  fun c ->
    let canon_st_comp_post c1 =
      match Pulse_Syntax_Pure.inspect_term c1.Pulse_Syntax_Base.post with
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
    | Pulse_Syntax_Base.C_STGhost (i, s) ->
        Pulse_Syntax_Base.C_STGhost (i, (canon_st_comp_post s))
let (typing_canon :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun t -> fun c -> fun d -> d
let (try_frame_pre_uvs :
  Prims.bool ->
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
  fun allow_ambiguous ->
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
                           (Prims.of_int (493)) (Prims.of_int (22))
                           (Prims.of_int (493)) (Prims.of_int (23)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                           (Prims.of_int (491)) (Prims.of_int (42))
                           (Prims.of_int (564)) (Prims.of_int (88)))))
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
                                          (Prims.of_int (495))
                                          (Prims.of_int (10))
                                          (Prims.of_int (495))
                                          (Prims.of_int (48)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.fst"
                                          (Prims.of_int (495))
                                          (Prims.of_int (51))
                                          (Prims.of_int (564))
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
                                                     (Prims.of_int (498))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (498))
                                                     (Prims.of_int (75)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.fst"
                                                     (Prims.of_int (495))
                                                     (Prims.of_int (51))
                                                     (Prims.of_int (564))
                                                     (Prims.of_int (88)))))
                                            (Obj.magic
                                               (prove allow_ambiguous g1 ctxt
                                                  () uvs
                                                  (Pulse_Syntax_Base.comp_pre
                                                     c) ()))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | FStar_Pervasives.Mkdtuple5
                                                      (g11, nts,
                                                       effect_labels,
                                                       remaining_ctxt,
                                                       k_frame)
                                                      ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (49)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (564))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Substs.nt_subst_st_term
                                                                    t nts))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (516))
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
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (515))
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
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (514))
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
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (564))
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
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (104)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (564))
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
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
            (unit, unit, unit) Pulse_Typing.st_typing)
            FStar_Pervasives.dtuple3 ->
            Pulse_Syntax_Base.ppname ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_ambiguous ->
    fun g ->
      fun ctxt ->
        fun ctxt_typing ->
          fun d ->
            fun res_ppname ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (575)) (Prims.of_int (12))
                         (Prims.of_int (575)) (Prims.of_int (32)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (577)) (Prims.of_int (2))
                         (Prims.of_int (577)) (Prims.of_int (64)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g)))
                (fun uu___ ->
                   (fun uvs ->
                      Obj.magic
                        (try_frame_pre_uvs allow_ambiguous g ctxt () uvs d
                           res_ppname)) uu___)
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
                       (Prims.of_int (586)) (Prims.of_int (10))
                       (Prims.of_int (586)) (Prims.of_int (46)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (588)) (Prims.of_int (2))
                       (Prims.of_int (641)) (Prims.of_int (99)))))
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
                                         (Prims.of_int (591))
                                         (Prims.of_int (79))
                                         (Prims.of_int (591))
                                         (Prims.of_int (80)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.fst"
                                         (Prims.of_int (590))
                                         (Prims.of_int (21))
                                         (Prims.of_int (641))
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
                                                        (Prims.of_int (593))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (593))
                                                        (Prims.of_int (44)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (593))
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (641))
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
                                                                   (Prims.of_int (594))
                                                                   (Prims.of_int (27))
                                                                   (Prims.of_int (594))
                                                                   (Prims.of_int (66)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.fst"
                                                                   (Prims.of_int (597))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (641))
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
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
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
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
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
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (prove
                                                                    false g2
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
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (check_equiv_emp'
                                                                    g3
                                                                    remaining_ctxt))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
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
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_doc
                                                                    remaining_ctxt))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.align
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Inferred postcondition additionally contains")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6;
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
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (Pulse_PP.text
                                                                    "Error in proving postcondition")
                                                                    :: uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                    uu___6))
                                                                    uu___6)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    uu___5)))
                                                                    uu___3)))))
                                                               uu___1)))
                                                    uu___1))) uu___)))) uu___)