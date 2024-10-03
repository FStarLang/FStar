open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (check_equiv_emp' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
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
                    (let uu___ =
                       Pulse_Typing_Util.check_equiv_now_nosmt
                         (Pulse_Typing.elab_env g) p Pulse_Syntax_Pure.tm_emp in
                     FStar_Tactics_Effect.tac_bind
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
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match uu___1 with
                               | (FStar_Pervasives_Native.Some tok, uu___3)
                                   -> FStar_Pervasives_Native.Some ()
                               | (FStar_Pervasives_Native.None, uu___3) ->
                                   FStar_Pervasives_Native.None))))) uu___1
        uu___
let (elim_exists_and_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
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
        let uu___ = Pulse_Checker_Prover_ElimExists.elim_exists g ctxt () in
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
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Pervasives.Mkdtuple4 (g1, ctxt1, d1, k1) ->
                    let uu___2 =
                      Pulse_Checker_Prover_ElimPure.elim_pure g1 ctxt1 () in
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
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 ->
                                 match uu___3 with
                                 | FStar_Pervasives.Mkdtuple4
                                     (g2, ctxt2, d2, k2) ->
                                     FStar_Pervasives.Mkdtuple4
                                       (g2, ctxt2, (),
                                         (Pulse_Checker_Base.k_elab_trans g
                                            g1 g2 ctxt ctxt1 ctxt2 k1 k2))))))
               uu___1)
let (unsolved_equiv_pst :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.slprop Prims.list ->
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
    Pulse_Syntax_Base.slprop Prims.list ->
      (Pulse_Syntax_Base.slprop Prims.list,
        Pulse_Syntax_Base.slprop Prims.list, unit) FStar_Pervasives.dtuple3)
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
    Pulse_Syntax_Base.slprop Prims.list ->
      (Pulse_Syntax_Base.slprop Prims.list,
        Pulse_Syntax_Base.slprop Prims.list, unit) FStar_Pervasives.dtuple3)
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
                         let uu___ =
                           Pulse_Checker_Prover_IntroPure.intro_pure preamble
                             pst p1 unsolved' () in
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
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun pst_opt ->
                                 match pst_opt with
                                 | FStar_Pervasives_Native.None ->
                                     let uu___1 =
                                       let uu___2 =
                                         let uu___3 =
                                           Pulse_PP.pp
                                             Pulse_PP.printable_term p1 in
                                         FStar_Tactics_Effect.tac_bind
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
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                     (Pulse_PP.text
                                                        "Cannot prove pure proposition")
                                                     uu___4)) in
                                       FStar_Tactics_Effect.tac_bind
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
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> [uu___3])) in
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
                                          (Obj.magic uu___1)
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                Obj.magic
                                                  (Pulse_Typing_Env.fail_doc
                                                     pst.Pulse_Checker_Prover_Base.pg
                                                     FStar_Pervasives_Native.None
                                                     uu___2)) uu___2))
                                 | FStar_Pervasives_Native.Some pst1 ->
                                     let uu___1 = prove_pures preamble pst1 in
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
                                          (Obj.magic uu___1)
                                          (fun pst2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> pst2)))) uu___1)
                     | uu___ ->
                         let uu___1 =
                           let uu___2 =
                             Pulse_Syntax_Printer.term_to_string
                               (FStar_List_Tot_Base.hd
                                  pst.Pulse_Checker_Prover_Base.unsolved) in
                           FStar_Tactics_Effect.tac_bind
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
                                   (FStar_Range.mk_range "Prims.fst"
                                      (Prims.of_int (611))
                                      (Prims.of_int (19))
                                      (Prims.of_int (611))
                                      (Prims.of_int (31)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     Prims.strcat
                                       "Impossible! prover.prove_pures: "
                                       (Prims.strcat uu___3
                                          " is not a pure, please file a bug-report"))) in
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
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 Obj.magic
                                   (Pulse_Typing_Env.fail
                                      pst.Pulse_Checker_Prover_Base.pg
                                      FStar_Pervasives_Native.None uu___2))
                                uu___2)))) uu___1 uu___
let (normalize_slprop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      ((Pulse_Syntax_Base.slprop, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun v ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                [FStar_Pervasives.unascribe;
                FStar_Pervasives.primops;
                FStar_Pervasives.iota])) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (131)) (Prims.of_int (14))
                 (Prims.of_int (131)) (Prims.of_int (51)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (131)) (Prims.of_int (54))
                 (Prims.of_int (138)) (Prims.of_int (22)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun steps ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_List_Tot_Base.op_At steps
                          [FStar_Pervasives.delta_attr
                             ["Pulse.Lib.Core.pulse_unfold"]])) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (134)) (Prims.of_int (14))
                            (Prims.of_int (134)) (Prims.of_int (66)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (134)) (Prims.of_int (69))
                            (Prims.of_int (138)) (Prims.of_int (22)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun steps1 ->
                         let uu___2 =
                           FStar_Tactics_V2_Builtins.norm_well_typed_term
                             (Pulse_Typing.elab_env g) steps1 v in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (136))
                                       (Prims.of_int (11))
                                       (Prims.of_int (136))
                                       (Prims.of_int (54)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (138))
                                       (Prims.of_int (2))
                                       (Prims.of_int (138))
                                       (Prims.of_int (22)))))
                              (Obj.magic uu___2)
                              (fun v' ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> Prims.Mkdtuple2 (v', ())))))
                        uu___2))) uu___1)
let (normalize_slprop_welltyped :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      unit ->
        ((Pulse_Syntax_Base.slprop, unit, unit) FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun v ->
      fun v_typing ->
        let uu___ = normalize_slprop g v in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                   (Prims.of_int (146)) (Prims.of_int (29))
                   (Prims.of_int (146)) (Prims.of_int (49)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                   (Prims.of_int (145)) Prims.int_one (Prims.of_int (148))
                   (Prims.of_int (35))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 ->
                  match uu___1 with
                  | Prims.Mkdtuple2 (v', v_equiv_v') ->
                      FStar_Pervasives.Mkdtuple3 (v', (), ())))
let (normalize_slprop_context :
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
             (fun uu___1 -> pst.Pulse_Checker_Prover_Base.remaining_ctxt)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (156)) (Prims.of_int (13))
                 (Prims.of_int (156)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (156)) (Prims.of_int (34))
                 (Prims.of_int (176)) (Prims.of_int (3))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun ctxt ->
              let uu___1 =
                FStar_Tactics_Util.map
                  (fun v ->
                     let uu___2 =
                       normalize_slprop pst.Pulse_Checker_Prover_Base.pg v in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                                (Prims.of_int (157)) (Prims.of_int (49))
                                (Prims.of_int (157)) (Prims.of_int (76)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                                (Prims.of_int (157)) (Prims.of_int (49))
                                (Prims.of_int (157)) (Prims.of_int (79)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 ->
                               Prims.__proj__Mkdtuple2__item___1 uu___3)))
                  ctxt in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (157)) (Prims.of_int (14))
                            (Prims.of_int (157)) (Prims.of_int (80)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (157)) (Prims.of_int (83))
                            (Prims.of_int (176)) (Prims.of_int (3)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun ctxt' ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   pst.Pulse_Checker_Prover_Base.unsolved)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (159))
                                       (Prims.of_int (17))
                                       (Prims.of_int (159))
                                       (Prims.of_int (29)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (159))
                                       (Prims.of_int (32))
                                       (Prims.of_int (176))
                                       (Prims.of_int (3)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun unsolved ->
                                    let uu___3 =
                                      FStar_Tactics_Util.map
                                        (fun v ->
                                           let uu___4 =
                                             normalize_slprop
                                               pst.Pulse_Checker_Prover_Base.pg
                                               v in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.fst"
                                                      (Prims.of_int (160))
                                                      (Prims.of_int (57))
                                                      (Prims.of_int (160))
                                                      (Prims.of_int (84)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.fst"
                                                      (Prims.of_int (160))
                                                      (Prims.of_int (57))
                                                      (Prims.of_int (160))
                                                      (Prims.of_int (87)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___6 ->
                                                     Prims.__proj__Mkdtuple2__item___1
                                                       uu___5))) unsolved in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.fst"
                                                  (Prims.of_int (160))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (160))
                                                  (Prims.of_int (88)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.fst"
                                                  (Prims.of_int (162))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (176))
                                                  (Prims.of_int (3)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun unsolved' ->
                                               let uu___4 =
                                                 if
                                                   Pulse_RuntimeUtils.debug_at_level
                                                     (Pulse_Typing_Env.fstar_env
                                                        pst.Pulse_Checker_Prover_Base.pg)
                                                     "ggg"
                                                 then
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___5 =
                                                           let uu___6 =
                                                             let uu___7 =
                                                               Pulse_PP.pp
                                                                 (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                 ctxt in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (11)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                               (Obj.magic
                                                                  uu___7)
                                                               (fun uu___8 ->
                                                                  (fun uu___8
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    ctxt' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    [uu___11])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> uu___8
                                                                    ::
                                                                    uu___10))))
                                                                    uu___8) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___8
                                                                    ->
                                                                    (Pulse_PP.text
                                                                    "PROVER Normalized context")
                                                                    :: uu___7)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (3)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun uu___6 ->
                                                                 Obj.magic
                                                                   (Pulse_Typing_Env.info_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    uu___6))
                                                                uu___6)))
                                                 else
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 -> ()))) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.fst"
                                                             (Prims.of_int (162))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (167))
                                                             (Prims.of_int (3)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.fst"
                                                             (Prims.of_int (169))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (175))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic uu___4)
                                                    (fun uu___5 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___6 ->
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
                                                                    (Pulse_Syntax_Pure.list_as_slprop
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
                                                                    (Pulse_Syntax_Pure.list_as_slprop
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
                                                            })))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
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
                                 (let uu___1 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Pulse_Checker_Prover_Base.op_Array_Access
                                              pst.Pulse_Checker_Prover_Base.ss
                                              hd)) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (193))
                                             (Prims.of_int (15))
                                             (Prims.of_int (193))
                                             (Prims.of_int (26)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (194))
                                             (Prims.of_int (6))
                                             (Prims.of_int (207))
                                             (Prims.of_int (43)))))
                                    (Obj.magic uu___1)
                                    (fun uu___2 ->
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
                                          | uu___2 ->
                                              let uu___3 =
                                                Obj.magic
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
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
                                                        })) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (203))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (205))
                                                            (Prims.of_int (30)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (207))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (207))
                                                            (Prims.of_int (43)))))
                                                   (Obj.magic uu___3)
                                                   (fun uu___4 ->
                                                      (fun pst1 ->
                                                         Obj.magic
                                                           (__intro_any_exists
                                                              (n -
                                                                 Prims.int_one)
                                                              preamble pst1
                                                              prover)) uu___4)))
                                         uu___2))))) uu___3 uu___2 uu___1
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
type ('preamble, 'pst0) prover_iteration_res_t =
  | Stepped of unit Pulse_Checker_Prover_Base.prover_state 
  | NoProgress 
let (uu___is_Stepped :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit, unit) prover_iteration_res_t -> Prims.bool)
  =
  fun preamble ->
    fun pst0 ->
      fun projectee ->
        match projectee with | Stepped _0 -> true | uu___ -> false
let (__proj__Stepped__item___0 :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit, unit) prover_iteration_res_t ->
        unit Pulse_Checker_Prover_Base.prover_state)
  =
  fun preamble ->
    fun pst0 -> fun projectee -> match projectee with | Stepped _0 -> _0
let (uu___is_NoProgress :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit, unit) prover_iteration_res_t -> Prims.bool)
  =
  fun preamble ->
    fun pst0 ->
      fun projectee ->
        match projectee with | NoProgress -> true | uu___ -> false
let (res_advance :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      unit Pulse_Checker_Prover_Base.prover_state ->
        (unit, unit) prover_iteration_res_t ->
          (unit, unit) prover_iteration_res_t)
  =
  fun preamble ->
    fun pst0 ->
      fun pst1 ->
        fun ir ->
          match ir with
          | Stepped pst1' -> Stepped pst1'
          | NoProgress -> NoProgress
type prover_pass_t =
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr
type prover_pass =
  | P of Prims.string * prover_pass_t 
let (uu___is_P : prover_pass -> Prims.bool) = fun projectee -> true
let (__proj__P__item___0 : prover_pass -> Prims.string) =
  fun projectee -> match projectee with | P (_0, _1) -> _0
let (__proj__P__item___1 : prover_pass -> prover_pass_t) =
  fun projectee -> match projectee with | P (_0, _1) -> _1
let rec (prover_iteration_loop :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      prover_pass Prims.list ->
        ((unit, unit) prover_iteration_res_t, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun preamble ->
           fun pst0 ->
             fun passes ->
               match passes with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> NoProgress)))
               | (P (name, pass))::passes' ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = pass preamble pst0 in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (252)) (Prims.of_int (14))
                                    (Prims.of_int (252)) (Prims.of_int (23)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.fst"
                                    (Prims.of_int (253)) (Prims.of_int (4))
                                    (Prims.of_int (264)) (Prims.of_int (5)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun pst ->
                                 if pst.Pulse_Checker_Prover_Base.progress
                                 then
                                   let uu___1 =
                                     Pulse_Checker_Prover_Util.debug_prover
                                       pst.Pulse_Checker_Prover_Base.pg
                                       (fun uu___2 ->
                                          let uu___3 =
                                            Pulse_Show.show
                                              (Pulse_Show.tac_showable_list
                                                 Pulse_Show.tac_showable_r_term)
                                              pst.Pulse_Checker_Prover_Base.remaining_ctxt in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.fst"
                                                     (Prims.of_int (256))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (256))
                                                     (Prims.of_int (40)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Prims.fst"
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 ->
                                                    Prims.strcat
                                                      (Prims.strcat
                                                         "prover: "
                                                         (Prims.strcat name
                                                            ": made progress, remaining_ctxt after pass = "))
                                                      (Prims.strcat uu___4
                                                         "\n")))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (254))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (256))
                                                 (Prims.of_int (41)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (257))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (257))
                                                 (Prims.of_int (17)))))
                                        (Obj.magic uu___1)
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> Stepped pst)))
                                 else
                                   (let uu___2 =
                                      Pulse_Checker_Prover_Util.debug_prover
                                        pst.Pulse_Checker_Prover_Base.pg
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___4 ->
                                                      Prims.strcat "prover: "
                                                        (Prims.strcat name
                                                           ": no progress\n"))))
                                             uu___3) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.fst"
                                                  (Prims.of_int (259))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (260))
                                                  (Prims.of_int (56)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.fst"
                                                  (Prims.of_int (263))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (263))
                                                  (Prims.of_int (40)))))
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            (fun uu___3 ->
                                               Obj.magic
                                                 (prover_iteration_loop
                                                    preamble pst0 passes'))
                                              uu___3)))) uu___1)))) uu___2
          uu___1 uu___
let (prover_pass_collect_exists :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun preamble ->
         fun pst0 ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match collect_exists
                           (Pulse_Typing_Env.push_env
                              pst0.Pulse_Checker_Prover_Base.pg
                              pst0.Pulse_Checker_Prover_Base.uvs)
                           pst0.Pulse_Checker_Prover_Base.unsolved
                   with
                   | FStar_Pervasives.Mkdtuple3 (exs, rest, d) ->
                       unsolved_equiv_pst preamble pst0
                         (FStar_List_Tot_Base.op_At exs rest) ()))) uu___1
        uu___
let (prover_iteration :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      ((unit, unit) prover_iteration_res_t, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst0 ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> pst0)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (280)) (Prims.of_int (12))
                 (Prims.of_int (280)) (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (280)) (Prims.of_int (19))
                 (Prims.of_int (292)) (Prims.of_int (3))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun pst ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        {
                          Pulse_Checker_Prover_Base.pg =
                            (pst.Pulse_Checker_Prover_Base.pg);
                          Pulse_Checker_Prover_Base.remaining_ctxt =
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
                          Pulse_Checker_Prover_Base.goals_inv = ();
                          Pulse_Checker_Prover_Base.solved_inv = ();
                          Pulse_Checker_Prover_Base.progress = false;
                          Pulse_Checker_Prover_Base.allow_ambiguous =
                            (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                        })) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (281)) (Prims.of_int (14))
                            (Prims.of_int (281)) (Prims.of_int (39)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (283)) (Prims.of_int (2))
                            (Prims.of_int (292)) (Prims.of_int (3)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun pst1 ->
                         let uu___2 =
                           prover_iteration_loop preamble pst1
                             [P
                                ("elim_exists",
                                  Pulse_Checker_Prover_ElimExists.elim_exists_pst);
                             P ("collect_exists", prover_pass_collect_exists);
                             P
                               ("explode",
                                 Pulse_Checker_Prover_Explode.explode);
                             P
                               ("match_syntactic",
                                 Pulse_Checker_Prover_Match.match_syntactic);
                             P
                               ("match_fastunif",
                                 Pulse_Checker_Prover_Match.match_fastunif);
                             P
                               ("match_fastunif_i",
                                 Pulse_Checker_Prover_Match.match_fastunif_i);
                             P
                               ("match_full",
                                 Pulse_Checker_Prover_Match.match_full)] in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (283))
                                       (Prims.of_int (17))
                                       (Prims.of_int (292))
                                       (Prims.of_int (3)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.fst"
                                       (Prims.of_int (283))
                                       (Prims.of_int (2))
                                       (Prims.of_int (292))
                                       (Prims.of_int (3)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___4 ->
                                      res_advance preamble pst0 pst1 uu___3))))
                        uu___2))) uu___1)
let rec (prover :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst0 ->
      let uu___ =
        Pulse_Checker_Prover_Util.debug_prover
          pst0.Pulse_Checker_Prover_Base.pg
          (fun uu___1 ->
             let uu___2 =
               Pulse_Show.show Pulse_Show.tac_showable_bool
                 pst0.Pulse_Checker_Prover_Base.allow_ambiguous in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                        (Prims.of_int (304)) (Prims.of_int (6))
                        (Prims.of_int (304)) (Prims.of_int (33)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                        (Prims.of_int (301)) (Prims.of_int (4))
                        (Prims.of_int (304)) (Prims.of_int (33)))))
               (Obj.magic uu___2)
               (fun uu___3 ->
                  (fun uu___3 ->
                     let uu___4 =
                       let uu___5 =
                         Pulse_Show.show Pulse_Show.tac_showable_r_term
                           (Pulse_Syntax_Pure.list_as_slprop
                              pst0.Pulse_Checker_Prover_Base.unsolved) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (303)) (Prims.of_int (6))
                                  (Prims.of_int (303)) (Prims.of_int (43)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (301)) (Prims.of_int (4))
                                  (Prims.of_int (304)) (Prims.of_int (33)))))
                         (Obj.magic uu___5)
                         (fun uu___6 ->
                            (fun uu___6 ->
                               let uu___7 =
                                 let uu___8 =
                                   Pulse_Show.show
                                     Pulse_Show.tac_showable_r_term
                                     (Pulse_Syntax_Pure.list_as_slprop
                                        pst0.Pulse_Checker_Prover_Base.remaining_ctxt) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.fst"
                                            (Prims.of_int (302))
                                            (Prims.of_int (6))
                                            (Prims.of_int (302))
                                            (Prims.of_int (49)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Printf.fst"
                                            (Prims.of_int (122))
                                            (Prims.of_int (8))
                                            (Prims.of_int (124))
                                            (Prims.of_int (44)))))
                                   (Obj.magic uu___8)
                                   (fun uu___9 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___10 ->
                                           fun x ->
                                             fun x1 ->
                                               Prims.strcat
                                                 (Prims.strcat
                                                    (Prims.strcat
                                                       "At the prover top-level with remaining_ctxt: "
                                                       (Prims.strcat uu___9
                                                          "\n  unsolved: "))
                                                    (Prims.strcat x
                                                       "\n  allow_ambiguous: "))
                                                 (Prims.strcat x1 "\n"))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (301))
                                             (Prims.of_int (4))
                                             (Prims.of_int (304))
                                             (Prims.of_int (33)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (301))
                                             (Prims.of_int (4))
                                             (Prims.of_int (304))
                                             (Prims.of_int (33)))))
                                    (Obj.magic uu___7)
                                    (fun uu___8 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___9 -> uu___8 uu___6))))
                              uu___6) in
                     Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.fst"
                                   (Prims.of_int (301)) (Prims.of_int (4))
                                   (Prims.of_int (304)) (Prims.of_int (33)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.fst"
                                   (Prims.of_int (301)) (Prims.of_int (4))
                                   (Prims.of_int (304)) (Prims.of_int (33)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> uu___5 uu___3)))) uu___3)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (300)) (Prims.of_int (2)) (Prims.of_int (304))
                 (Prims.of_int (34)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                 (Prims.of_int (304)) (Prims.of_int (35))
                 (Prims.of_int (369)) (Prims.of_int (40)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 =
                Pulse_Checker_Prover_ElimPure.elim_pure_pst preamble pst0 in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (308)) (Prims.of_int (13))
                            (Prims.of_int (308)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                            (Prims.of_int (310)) (Prims.of_int (2))
                            (Prims.of_int (369)) (Prims.of_int (40)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun pst01 ->
                         match pst01.Pulse_Checker_Prover_Base.unsolved with
                         | [] ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> pst01)))
                         | uu___3 ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___4 =
                                     normalize_slprop_context preamble pst01 in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.fst"
                                              (Prims.of_int (319))
                                              (Prims.of_int (14))
                                              (Prims.of_int (319))
                                              (Prims.of_int (43)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.fst"
                                              (Prims.of_int (319))
                                              (Prims.of_int (46))
                                              (Prims.of_int (369))
                                              (Prims.of_int (40)))))
                                     (Obj.magic uu___4)
                                     (fun uu___5 ->
                                        (fun pst ->
                                           let uu___5 =
                                             Obj.magic
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___6 ->
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
                                                         (pst.Pulse_Checker_Prover_Base.unsolved);
                                                       Pulse_Checker_Prover_Base.k
                                                         =
                                                         (pst.Pulse_Checker_Prover_Base.k);
                                                       Pulse_Checker_Prover_Base.goals_inv
                                                         = ();
                                                       Pulse_Checker_Prover_Base.solved_inv
                                                         = ();
                                                       Pulse_Checker_Prover_Base.progress
                                                         = false;
                                                       Pulse_Checker_Prover_Base.allow_ambiguous
                                                         =
                                                         (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                     })) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (320))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (320))
                                                         (Prims.of_int (41)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.fst"
                                                         (Prims.of_int (322))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (369))
                                                         (Prims.of_int (40)))))
                                                (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun pst1 ->
                                                      let uu___6 =
                                                        prover_iteration
                                                          preamble pst1 in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (30)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                           (Obj.magic uu___6)
                                                           (fun uu___7 ->
                                                              (fun uu___7 ->
                                                                 match uu___7
                                                                 with
                                                                 | Stepped
                                                                    pst' ->
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst')
                                                                 | NoProgress
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    intro_any_exists
                                                                    preamble
                                                                    pst1
                                                                    prover in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun pst2
                                                                    ->
                                                                    if
                                                                    pst2.Pulse_Checker_Prover_Base.progress
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (prover
                                                                    preamble
                                                                    pst2))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    pst2.Pulse_Checker_Prover_Base.unsolved
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> pst2))
                                                                    | 
                                                                    hd::unsolved'
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    collect_pures
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst2.Pulse_Checker_Prover_Base.pg
                                                                    pst2.Pulse_Checker_Prover_Base.uvs)
                                                                    pst2.Pulse_Checker_Prover_Base.unsolved)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (pures,
                                                                    rest, d)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    unsolved_equiv_pst
                                                                    preamble
                                                                    pst2
                                                                    (FStar_List_Tot_Base.op_At
                                                                    rest
                                                                    pures) ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun pst3
                                                                    ->
                                                                    match 
                                                                    pst3.Pulse_Checker_Prover_Base.unsolved
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> pst3)))
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
                                                                    uu___13
                                                                    ->
                                                                    prove_pures
                                                                    preamble
                                                                    pst3
                                                                    | 
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_Util.filter
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Pure.uu___is_Tm_Pure
                                                                    (Pulse_Syntax_Pure.inspect_term
                                                                    t)))))
                                                                    uu___15)
                                                                    pst3.Pulse_Checker_Prover_Base.unsolved in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    non_pures
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun q1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst3.Pulse_Checker_Prover_Base.ss
                                                                    q1)))
                                                                    uu___16)
                                                                    non_pures in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    non_pures1
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst3.Pulse_Checker_Prover_Base.ss
                                                                    q)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    q_norm ->
                                                                    let uu___17
                                                                    =
                                                                    check_equiv_emp'
                                                                    pst3.Pulse_Checker_Prover_Base.pg
                                                                    q_norm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.uvs);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.ss);
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.nts);
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.solved);
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    =
                                                                    unsolved';
                                                                    Pulse_Checker_Prover_Base.k
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.k);
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.progress
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.progress);
                                                                    Pulse_Checker_Prover_Base.allow_ambiguous
                                                                    =
                                                                    (pst3.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun pst'
                                                                    ->
                                                                    Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst'))
                                                                    uu___20))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    Pulse_Syntax_Pure.canon_slprop_list_print
                                                                    non_pures1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___24)
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
                                                                    uu___25) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___24)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Cannot prove:")
                                                                    uu___23)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    Pulse_Syntax_Pure.canon_slprop_list_print
                                                                    pst3.Pulse_Checker_Prover_Base.remaining_ctxt in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    uu___28))
                                                                    uu___28) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___27)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___25)
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
                                                                    uu___26)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    [uu___25])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    uu___22
                                                                    ::
                                                                    uu___24))))
                                                                    uu___22) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    Pulse_Config.debug_flag
                                                                    "initial_solver_state" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    if
                                                                    uu___24
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    preamble.Pulse_Checker_Prover_Base.goals in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___28)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___26)
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
                                                                    uu___27)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___31)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "and initial context:")
                                                                    uu___30)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    [uu___29])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    uu___26
                                                                    ::
                                                                    uu___28))))
                                                                    uu___26)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    -> []))))
                                                                    uu___24) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___21
                                                                    uu___23))))
                                                                    uu___21) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    pst3.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    msg))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15))))
                                                                    uu___13)))
                                                                    uu___11)))))
                                                                    uu___9)))
                                                                uu___7)))
                                                     uu___6))) uu___5))))
                        uu___3))) uu___1)
let rec (get_q_at_hd :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop Prims.list ->
      Pulse_Syntax_Base.slprop ->
        (Pulse_Syntax_Base.slprop Prims.list, unit) Prims.dtuple2)
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
      Pulse_Syntax_Base.slprop ->
        unit ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.slprop ->
              unit ->
                ((Pulse_Typing_Env.env,
                   Pulse_Checker_Prover_Substs.nt_substs,
                   FStar_TypeChecker_Core.tot_or_ghost Prims.list,
                   Pulse_Syntax_Base.slprop,
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
                let uu___ =
                  Pulse_Checker_Prover_Util.debug_prover g
                    (fun uu___1 ->
                       let uu___2 = Pulse_Syntax_Printer.term_to_string goals in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (397)) (Prims.of_int (30))
                                  (Prims.of_int (397)) (Prims.of_int (54)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.fst"
                                  (Prims.of_int (396)) (Prims.of_int (4))
                                  (Prims.of_int (397)) (Prims.of_int (54)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___4 =
                                 let uu___5 =
                                   Pulse_Syntax_Printer.term_to_string ctxt in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.fst"
                                            (Prims.of_int (397))
                                            (Prims.of_int (6))
                                            (Prims.of_int (397))
                                            (Prims.of_int (29)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Printf.fst"
                                            (Prims.of_int (122))
                                            (Prims.of_int (8))
                                            (Prims.of_int (124))
                                            (Prims.of_int (44)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 ->
                                           fun x ->
                                             Prims.strcat
                                               (Prims.strcat
                                                  "\nEnter top-level prove with ctxt: "
                                                  (Prims.strcat uu___6
                                                     "\ngoals: "))
                                               (Prims.strcat x "\n"))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (396))
                                             (Prims.of_int (4))
                                             (Prims.of_int (397))
                                             (Prims.of_int (54)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.fst"
                                             (Prims.of_int (396))
                                             (Prims.of_int (4))
                                             (Prims.of_int (397))
                                             (Prims.of_int (54)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 -> uu___5 uu___3))))
                              uu___3)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                           (Prims.of_int (395)) (Prims.of_int (2))
                           (Prims.of_int (397)) (Prims.of_int (55)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                           (Prims.of_int (397)) (Prims.of_int (56))
                           (Prims.of_int (489)) (Prims.of_int (127)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        let uu___2 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  Pulse_Syntax_Pure.slprop_as_list ctxt)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.fst"
                                      (Prims.of_int (399))
                                      (Prims.of_int (15))
                                      (Prims.of_int (399))
                                      (Prims.of_int (34)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.fst"
                                      (Prims.of_int (414))
                                      (Prims.of_int (76))
                                      (Prims.of_int (489))
                                      (Prims.of_int (127)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun ctxt_l ->
                                   let uu___3 =
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 ->
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
                                             })) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (416))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (420))
                                                 (Prims.of_int (12)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.fst"
                                                 (Prims.of_int (423))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (489))
                                                 (Prims.of_int (127)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun preamble ->
                                              let uu___4 =
                                                Obj.magic
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___5 ->
                                                        {
                                                          Pulse_Checker_Prover_Base.pg
                                                            = g;
                                                          Pulse_Checker_Prover_Base.remaining_ctxt
                                                            =
                                                            (Pulse_Syntax_Pure.slprop_as_list
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
                                                            (Pulse_Syntax_Pure.slprop_as_list
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
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    (Pulse_Syntax_Pure.slprop_as_list
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
                                                            = allow_ambiguous
                                                        })) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (425))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (437))
                                                            (Prims.of_int (40)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.fst"
                                                            (Prims.of_int (438))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (489))
                                                            (Prims.of_int (127)))))
                                                   (Obj.magic uu___4)
                                                   (fun uu___5 ->
                                                      (fun pst0 ->
                                                         let uu___5 =
                                                           prover preamble
                                                             pst0 in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (25)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (127)))))
                                                              (Obj.magic
                                                                 uu___5)
                                                              (fun uu___6 ->
                                                                 (fun pst ->
                                                                    let uu___6
                                                                    =
                                                                    match 
                                                                    pst.Pulse_Checker_Prover_Base.nts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nts ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    nts)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    Pulse_Checker_Prover_Substs.ss_to_nt_substs
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.uvs
                                                                    pst.Pulse_Checker_Prover_Base.ss in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (460))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    msg ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_env
                                                                    pst.Pulse_Checker_Prover_Base.pg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.pg =")
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_env
                                                                    pst.Pulse_Checker_Prover_Base.uvs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.uvs =")
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_Checker_Prover_Substs.pp_ss_t
                                                                    pst.Pulse_Checker_Prover_Base.ss in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.ss =")
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.remaining_ctxt =")
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.unsolved in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "pst.unsolved =")
                                                                    uu___24)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    [uu___23])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    uu___20
                                                                    ::
                                                                    uu___22))))
                                                                    uu___20) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    uu___17
                                                                    ::
                                                                    uu___19))))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    uu___14
                                                                    ::
                                                                    uu___16))))
                                                                    uu___14) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___11
                                                                    ::
                                                                    uu___13))))
                                                                    uu___11) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (Pulse_PP.text
                                                                    (Prims.strcat
                                                                    "Prover error: ill-typed substitutions ("
                                                                    (Prims.strcat
                                                                    msg ")")))
                                                                    ::
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    uu___9))
                                                                    uu___9)))
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    nts ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    nts))))
                                                                    uu___8))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (127)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
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
                                                                    (Pulse_Syntax_Pure.list_as_slprop
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
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    Pulse_Syntax_Pure.tm_emp)
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    nts))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    goals
                                                                    nts_uvs)
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    () ())))))))
                                                                   uu___6)))
                                                        uu___5))) uu___4)))
                                  uu___3))) uu___1)
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
      Pulse_Syntax_Base.slprop ->
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
                let uu___ =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> d)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                           (Prims.of_int (518)) (Prims.of_int (22))
                           (Prims.of_int (518)) (Prims.of_int (23)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                           (Prims.of_int (516)) (Prims.of_int (42))
                           (Prims.of_int (589)) (Prims.of_int (88)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Pervasives.Mkdtuple3 (t, c, d1) ->
                            let uu___2 =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 ->
                                      Pulse_Typing_Env.push_context g
                                        "try_frame_pre"
                                        t.Pulse_Syntax_Base.range1)) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.fst"
                                          (Prims.of_int (520))
                                          (Prims.of_int (10))
                                          (Prims.of_int (520))
                                          (Prims.of_int (48)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.fst"
                                          (Prims.of_int (520))
                                          (Prims.of_int (51))
                                          (Prims.of_int (589))
                                          (Prims.of_int (88)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun g1 ->
                                       let uu___3 =
                                         prove allow_ambiguous g1 ctxt () uvs
                                           (Pulse_Syntax_Base.comp_pre c) () in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.fst"
                                                     (Prims.of_int (523))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (523))
                                                     (Prims.of_int (75)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.fst"
                                                     (Prims.of_int (520))
                                                     (Prims.of_int (51))
                                                     (Prims.of_int (589))
                                                     (Prims.of_int (88)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  match uu___4 with
                                                  | FStar_Pervasives.Mkdtuple5
                                                      (g11, nts,
                                                       effect_labels,
                                                       remaining_ctxt,
                                                       k_frame)
                                                      ->
                                                      let uu___5 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___6 ->
                                                                Pulse_Typing_Metatheory.st_typing_weakening
                                                                  g1 uvs t c
                                                                  d1 g11)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (49)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun d2 ->
                                                                 let uu___6 =
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Checker_Prover_Substs.nt_subst_st_term
                                                                    t nts)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun t1
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Checker_Prover_Substs.nt_subst_comp
                                                                    c nts)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun c1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Checker_Prover_Substs.st_typing_nt_substs_derived
                                                                    g11 uvs t
                                                                    c d2 nts
                                                                    effect_labels)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    (x, x_t)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    x_t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    t1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (539))
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
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover error: for term "
                                                                    (Prims.strcat
                                                                    uu___15
                                                                    ", implicit solution "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " has ghost effect"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    uu___14
                                                                    uu___12))))
                                                                    uu___12) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g11
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t1.Pulse_Syntax_Base.range1))
                                                                    uu___11))
                                                                    uu___11)))
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    d3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> d3))))
                                                                    uu___10) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun d3
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    canon_post
                                                                    c1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (546))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (546))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (546))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun c2
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    typing_canon
                                                                    g11 t1 c1
                                                                    d3)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun d4
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    coerce_eq
                                                                    k_frame
                                                                    ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    k_frame1
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g11)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Pulse_Syntax_Base.comp_res
                                                                    c2)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun ty
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g11 x
                                                                    res_ppname
                                                                    ty)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun g2
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2)
                                                                    (res_ppname,
                                                                    x))
                                                                    remaining_ctxt)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    ctxt' ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Typing_Metatheory.st_typing_weakening_standard
                                                                    g11 t1
                                                                    (canon_post
                                                                    c1) d4
                                                                    g11)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun d5
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Pulse_Checker_Base.continuation_elaborator_with_bind
                                                                    g11
                                                                    remaining_ctxt
                                                                    c2 t1 d5
                                                                    ()
                                                                    (res_ppname,
                                                                    x) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (104)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
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
                                                                    uu___19,
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
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                uu___6)))
                                                 uu___4))) uu___3))) uu___1)
let (try_frame_pre :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.slprop ->
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
              let uu___ =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        Pulse_Typing_Env.mk_env
                          (Pulse_Typing_Env.fstar_env g))) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (600)) (Prims.of_int (12))
                         (Prims.of_int (600)) (Prims.of_int (32)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                         (Prims.of_int (602)) (Prims.of_int (2))
                         (Prims.of_int (602)) (Prims.of_int (64)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uvs ->
                      Obj.magic
                        (try_frame_pre_uvs allow_ambiguous g ctxt () uvs d
                           res_ppname)) uu___1)
let (prove_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
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
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Pulse_Typing_Env.push_context g "prove_post_hint" rng)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (611)) (Prims.of_int (10))
                       (Prims.of_int (611)) (Prims.of_int (46)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.fst"
                       (Prims.of_int (613)) (Prims.of_int (2))
                       (Prims.of_int (666)) (Prims.of_int (99)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun g1 ->
                    match post_hint with
                    | FStar_Pervasives_Native.None ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> r)))
                    | FStar_Pervasives_Native.Some post_hint1 ->
                        Obj.magic
                          (Obj.repr
                             (let uu___1 =
                                Obj.magic
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> r)) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.fst"
                                         (Prims.of_int (616))
                                         (Prims.of_int (79))
                                         (Prims.of_int (616))
                                         (Prims.of_int (80)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.fst"
                                         (Prims.of_int (615))
                                         (Prims.of_int (21))
                                         (Prims.of_int (666))
                                         (Prims.of_int (99)))))
                                (Obj.magic uu___1)
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      match uu___2 with
                                      | FStar_Pervasives.Mkdtuple5
                                          (x, g2, FStar_Pervasives.Mkdtuple3
                                           (u_ty, ty, ty_typing),
                                           Prims.Mkdtuple2
                                           (ctxt', ctxt'_typing), k)
                                          ->
                                          let uu___3 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                      "_posth")) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (618))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (618))
                                                        (Prims.of_int (44)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.fst"
                                                        (Prims.of_int (618))
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (666))
                                                        (Prims.of_int (99)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun ppname ->
                                                     let uu___4 =
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               Pulse_Syntax_Naming.open_term_nv
                                                                 post_hint1.Pulse_Typing.post
                                                                 (ppname, x))) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.fst"
                                                                   (Prims.of_int (619))
                                                                   (Prims.of_int (27))
                                                                   (Prims.of_int (619))
                                                                   (Prims.of_int (66)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.fst"
                                                                   (Prims.of_int (622))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (666))
                                                                   (Prims.of_int (99)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
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
                                                                    (let uu___5
                                                                    =
                                                                    let uu___6
                                                                    =
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    post_hint1.Pulse_Typing.ret_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "does not match the expected")
                                                                    uu___13)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___10
                                                                    uu___12))))
                                                                    uu___10) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "The return type")
                                                                    uu___9)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [uu___8])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (Pulse_PP.text
                                                                    "Error in proving postcondition")
                                                                    :: uu___7)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___5)
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
                                                                    uu___6 ->
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
                                                                    (let uu___7
                                                                    =
                                                                    prove
                                                                    false g2
                                                                    ctxt' ()
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g2))
                                                                    post_hint_opened
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (g3, nts,
                                                                    uu___9,
                                                                    remaining_ctxt,
                                                                    k_post)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    coerce_eq
                                                                    k_post ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    k_post1
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    check_equiv_emp'
                                                                    g3
                                                                    remaining_ctxt in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_doc
                                                                    remaining_ctxt in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Pprint.align
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Inferred postcondition additionally contains")
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    [uu___16;
                                                                    if
                                                                    Pulse_Syntax_Pure.uu___is_Tm_Star
                                                                    (Pulse_Syntax_Pure.inspect_term
                                                                    remaining_ctxt)
                                                                    then
                                                                    Pulse_PP.text
                                                                    "Did you forget to free these resources?"
                                                                    else
                                                                    Pulse_PP.text
                                                                    "Did you forget to free this resource?"])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (Pulse_PP.text
                                                                    "Error in proving postcondition")
                                                                    ::
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                    uu___14))
                                                                    uu___14)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
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
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___8)))))
                                                               uu___5)))
                                                    uu___4))) uu___2))))
                   uu___1)