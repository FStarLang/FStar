open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
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
            Pulse_Prover_Common.k = (pst.Pulse_Prover_Common.k);
            Pulse_Prover_Common.goals_inv = ();
            Pulse_Prover_Common.solved_inv = ()
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
            Pulse_Prover_Common.k =
              (Pulse_Checker_Common.k_elab_equiv
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
                       (Pulse_Typing_Combinators.list_as_vprop
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
                       (Pulse_Typing_Combinators.list_as_vprop
                          remaining_ctxt') preamble.Pulse_Prover_Common.frame)
                    (Pulse_Prover_Common.op_Array_Access
                       pst.Pulse_Prover_Common.ss
                       pst.Pulse_Prover_Common.solved))
                 pst.Pulse_Prover_Common.k () ());
            Pulse_Prover_Common.goals_inv = ();
            Pulse_Prover_Common.solved_inv = ()
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
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (35)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.fst"
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (89))
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
                                                              (Prims.of_int (82))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (82))
                                                              (Prims.of_int (69)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.fst"
                                                              (Prims.of_int (83))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (89))
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
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
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
let rec (prove_pures :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      (unit Pulse_Prover_Common.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun preamble ->
         fun pst ->
           match pst.Pulse_Prover_Common.unsolved with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> pst)))
           | { Pulse_Syntax_Base.t = Pulse_Syntax_Base.Tm_Pure p;
               Pulse_Syntax_Base.range1 = uu___;_}::unsolved' ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Prover.fst"
                                (Prims.of_int (98)) (Prims.of_int (18))
                                (Prims.of_int (98)) (Prims.of_int (57)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Prover.fst"
                                (Prims.of_int (99)) (Prims.of_int (4))
                                (Prims.of_int (106)) (Prims.of_int (12)))))
                       (Obj.magic
                          (Pulse_Prover_IntroPure.intro_pure preamble pst p
                             unsolved' ()))
                       (fun uu___1 ->
                          (fun pst_opt ->
                             match pst_opt with
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (100))
                                               (Prims.of_int (32))
                                               (Prims.of_int (100))
                                               (Prims.of_int (94)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (100))
                                               (Prims.of_int (15))
                                               (Prims.of_int (100))
                                               (Prims.of_int (94)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Prover.fst"
                                                     (Prims.of_int (100))
                                                     (Prims.of_int (73))
                                                     (Prims.of_int (100))
                                                     (Prims.of_int (93)))))
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
                                                  p))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Prims.strcat
                                                      "cannot prove pure "
                                                      (Prims.strcat uu___1
                                                         "\n")))))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (Pulse_Typing_Env.fail
                                                 pst.Pulse_Prover_Common.pg
                                                 FStar_Pervasives_Native.None
                                                 uu___1)) uu___1))
                             | FStar_Pervasives_Native.Some pst1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (102))
                                               (Prims.of_int (18))
                                               (Prims.of_int (102))
                                               (Prims.of_int (34)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (102))
                                               (Prims.of_int (11))
                                               (Prims.of_int (102))
                                               (Prims.of_int (15)))))
                                      (Obj.magic (prove_pures preamble pst1))
                                      (fun pst2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> pst2)))) uu___1)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (Pulse_Typing_Env.fail pst.Pulse_Prover_Common.pg
                       FStar_Pervasives_Native.None "prove_pures: not a pure")))
        uu___1 uu___
let rec (prover :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      (unit Pulse_Prover_Common.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Prover.fst" (Prims.of_int (116))
                 (Prims.of_int (2)) (Prims.of_int (119)) (Prims.of_int (55)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Prover.fst" (Prims.of_int (121))
                 (Prims.of_int (2)) (Prims.of_int (160)) (Prims.of_int (32)))))
        (Obj.magic
           (Pulse_Prover_Common.debug_prover pst0.Pulse_Prover_Common.pg
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Prover.fst"
                            (Prims.of_int (119)) (Prims.of_int (6))
                            (Prims.of_int (119)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Prover.fst"
                            (Prims.of_int (117)) (Prims.of_int (4))
                            (Prims.of_int (119)) (Prims.of_int (54)))))
                   (Obj.magic
                      (Pulse_Syntax_Printer.term_to_string
                         (Pulse_Typing_Combinators.list_as_vprop
                            pst0.Pulse_Prover_Common.unsolved)))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Prover.fst"
                                       (Prims.of_int (117))
                                       (Prims.of_int (4))
                                       (Prims.of_int (119))
                                       (Prims.of_int (54)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Prover.fst"
                                       (Prims.of_int (117))
                                       (Prims.of_int (4))
                                       (Prims.of_int (119))
                                       (Prims.of_int (54)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.fst"
                                             (Prims.of_int (118))
                                             (Prims.of_int (6))
                                             (Prims.of_int (118))
                                             (Prims.of_int (60)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Printf.fst"
                                             (Prims.of_int (121))
                                             (Prims.of_int (8))
                                             (Prims.of_int (123))
                                             (Prims.of_int (44)))))
                                    (Obj.magic
                                       (Pulse_Syntax_Printer.term_to_string
                                          (Pulse_Typing_Combinators.list_as_vprop
                                             pst0.Pulse_Prover_Common.remaining_ctxt)))
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
              match pst0.Pulse_Prover_Common.unsolved with
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
                                (FStar_Range.mk_range "Pulse.Prover.fst"
                                   (Prims.of_int (124)) (Prims.of_int (14))
                                   (Prims.of_int (124)) (Prims.of_int (45)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Prover.fst"
                                   (Prims.of_int (126)) (Prims.of_int (4))
                                   (Prims.of_int (160)) (Prims.of_int (32)))))
                          (Obj.magic
                             (Pulse_Prover_ElimExists.elim_exists_pst
                                preamble pst0))
                          (fun uu___2 ->
                             (fun pst ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Prover.fst"
                                              (Prims.of_int (126))
                                              (Prims.of_int (4))
                                              (Prims.of_int (128))
                                              (Prims.of_int (62)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Prover.fst"
                                              (Prims.of_int (128))
                                              (Prims.of_int (63))
                                              (Prims.of_int (160))
                                              (Prims.of_int (32)))))
                                     (Obj.magic
                                        (Pulse_Prover_Common.debug_prover
                                           pst.Pulse_Prover_Common.pg
                                           (fun uu___2 ->
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Prover.fst"
                                                         (Prims.of_int (128))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (128))
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
                                                         pst.Pulse_Prover_Common.remaining_ctxt)))
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
                                                         "Pulse.Prover.fst"
                                                         (Prims.of_int (130))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (130))
                                                         (Prims.of_int (40)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Prover.fst"
                                                         (Prims.of_int (132))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (160))
                                                         (Prims.of_int (32)))))
                                                (Obj.magic
                                                   (Pulse_Prover_ElimPure.elim_pure_pst
                                                      preamble pst))
                                                (fun uu___3 ->
                                                   (fun pst1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (62)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
                                                           (Obj.magic
                                                              (Pulse_Prover_Common.debug_prover
                                                                 pst1.Pulse_Prover_Common.pg
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (134))
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
                                                                    pst1.Pulse_Prover_Common.remaining_ctxt)))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    collect_exists
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst1.Pulse_Prover_Common.pg
                                                                    pst1.Pulse_Prover_Common.uvs)
                                                                    pst1.Pulse_Prover_Common.unsolved))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover_Common.debug_prover
                                                                    pst1.Pulse_Prover_Common.pg
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (140))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover_Common.debug_prover
                                                                    pst2.Pulse_Prover_Common.pg
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (146))
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
                                                                    pst2.Pulse_Prover_Common.unsolved)))
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
                                                                    pst2.Pulse_Prover_Common.unsolved
                                                                    with
                                                                    | 
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, b,
                                                                    body);
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___7;_}::unsolved'
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Prover_IntroExists.intro_exists
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    collect_pures
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst2.Pulse_Prover_Common.pg
                                                                    pst2.Pulse_Prover_Common.uvs)
                                                                    pst2.Pulse_Prover_Common.unsolved))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
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
                                                                    pst3.Pulse_Prover_Common.unsolved
                                                                    with
                                                                    | 
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    uu___9;
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___10;_}::tl
                                                                    ->
                                                                    Obj.magic
                                                                    (prove_pures
                                                                    preamble
                                                                    pst3)
                                                                    | 
                                                                    q::tl ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (match_q
                                                                    preamble
                                                                    pst3 q tl
                                                                    ()
                                                                    Prims.int_zero))
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                uu___3)))
                                                     uu___3))) uu___2)))
                               uu___2)))) uu___)
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Prover_Substs.nt_substs,
                 Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit)
                   Pulse_Checker_Common.continuation_elaborator)
                 FStar_Pervasives.dtuple4,
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
                         (Prims.of_int (174)) (Prims.of_int (2))
                         (Prims.of_int (176)) (Prims.of_int (55)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (176)) (Prims.of_int (56))
                         (Prims.of_int (224)) (Prims.of_int (95)))))
                (Obj.magic
                   (Pulse_Prover_Common.debug_prover g
                      (fun uu___ ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (176)) (Prims.of_int (30))
                                    (Prims.of_int (176)) (Prims.of_int (54)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (175)) (Prims.of_int (4))
                                    (Prims.of_int (176)) (Prims.of_int (54)))))
                           (Obj.magic
                              (Pulse_Syntax_Printer.term_to_string goals))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (175))
                                               (Prims.of_int (4))
                                               (Prims.of_int (176))
                                               (Prims.of_int (54)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (175))
                                               (Prims.of_int (4))
                                               (Prims.of_int (176))
                                               (Prims.of_int (54)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Prover.fst"
                                                     (Prims.of_int (176))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (176))
                                                     (Prims.of_int (29)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Printf.fst"
                                                     (Prims.of_int (121))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (123))
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
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (178)) (Prims.of_int (59))
                                    (Prims.of_int (178)) (Prims.of_int (67)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (178)) (Prims.of_int (70))
                                    (Prims.of_int (224)) (Prims.of_int (95)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> ()))
                           (fun uu___1 ->
                              (fun ctxt_frame_typing ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (180))
                                               (Prims.of_int (4))
                                               (Prims.of_int (184))
                                               (Prims.of_int (10)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (187))
                                               (Prims.of_int (41))
                                               (Prims.of_int (224))
                                               (Prims.of_int (95)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            {
                                              Pulse_Prover_Common.g0 = g;
                                              Pulse_Prover_Common.ctxt = ctxt;
                                              Pulse_Prover_Common.frame =
                                                Pulse_Syntax_Base.tm_emp;
                                              Pulse_Prover_Common.ctxt_frame_typing
                                                = ();
                                              Pulse_Prover_Common.goals =
                                                goals
                                            }))
                                      (fun uu___1 ->
                                         (fun preamble ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.fst"
                                                          (Prims.of_int (189))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (198))
                                                          (Prims.of_int (19)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.fst"
                                                          (Prims.of_int (199))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (95)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       {
                                                         Pulse_Prover_Common.pg
                                                           = g;
                                                         Pulse_Prover_Common.remaining_ctxt
                                                           =
                                                           (Pulse_Typing_Combinators.vprop_as_list
                                                              ctxt);
                                                         Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                           = ();
                                                         Pulse_Prover_Common.uvs
                                                           = uvs;
                                                         Pulse_Prover_Common.ss
                                                           =
                                                           Pulse_Prover_Substs.empty;
                                                         Pulse_Prover_Common.solved
                                                           =
                                                           Pulse_Syntax_Base.tm_emp;
                                                         Pulse_Prover_Common.unsolved
                                                           =
                                                           (Pulse_Typing_Combinators.vprop_as_list
                                                              goals);
                                                         Pulse_Prover_Common.k
                                                           =
                                                           (Pulse_Checker_Common.k_elab_equiv
                                                              g g ctxt
                                                              (Pulse_Prover_Common.op_Star
                                                                 preamble.Pulse_Prover_Common.ctxt
                                                                 preamble.Pulse_Prover_Common.frame)
                                                              ctxt
                                                              (Pulse_Prover_Common.op_Star
                                                                 (Pulse_Prover_Common.op_Star
                                                                    (
                                                                    Pulse_Typing_Combinators.list_as_vprop
                                                                    (Pulse_Typing_Combinators.vprop_as_list
                                                                    ctxt))
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                 (Pulse_Prover_Common.op_Array_Access
                                                                    Pulse_Prover_Substs.empty
                                                                    Pulse_Syntax_Base.tm_emp))
                                                              (Pulse_Checker_Common.k_elab_unit
                                                                 g ctxt) ()
                                                              ());
                                                         Pulse_Prover_Common.goals_inv
                                                           = ();
                                                         Pulse_Prover_Common.solved_inv
                                                           = ()
                                                       }))
                                                 (fun uu___1 ->
                                                    (fun pst0 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (23)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (95)))))
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
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (95)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover_Substs.ss_to_nt_substs
                                                                    pst.Pulse_Prover_Common.pg
                                                                    pst.Pulse_Prover_Common.uvs
                                                                    pst.Pulse_Prover_Common.ss))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun ropt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (95)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    ropt
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst.Pulse_Prover_Common.pg
                                                                    FStar_Pervasives_Native.None
                                                                    "prove: ss not well-typed"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nts ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    ((pst.Pulse_Prover_Common.pg),
                                                                    (Pulse_Prover_Substs.well_typed_nt_substs_prefix
                                                                    pst.Pulse_Prover_Common.pg
                                                                    pst.Pulse_Prover_Common.uvs
                                                                    nts uvs),
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt),
                                                                    (Pulse_Checker_Common.k_elab_equiv
                                                                    g
                                                                    pst.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    ctxt
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    ctxt
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    (Pulse_Prover_Substs.nt_subst_term
                                                                    pst.Pulse_Prover_Common.solved
                                                                    nts))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Substs.nt_subst_term
                                                                    goals
                                                                    (Pulse_Prover_Substs.well_typed_nt_substs_prefix
                                                                    pst.Pulse_Prover_Common.pg
                                                                    pst.Pulse_Prover_Common.uvs
                                                                    nts uvs))
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt))
                                                                    pst.Pulse_Prover_Common.k
                                                                    () ()))))))
                                                                    uu___1)))
                                                                 uu___1)))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)
let (try_frame_pre_uvs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.comp_st ->
              (unit, unit, unit) Pulse_Typing.st_typing ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun uvs ->
          fun t ->
            fun c ->
              fun d ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.fst"
                           (Prims.of_int (235)) (Prims.of_int (4))
                           (Prims.of_int (235)) (Prims.of_int (50)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.fst"
                           (Prims.of_int (232)) (Prims.of_int (42))
                           (Prims.of_int (270)) (Prims.of_int (27)))))
                  (Obj.magic
                     (prove g ctxt () uvs (Pulse_Syntax_Base.comp_pre c) ()))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | FStar_Pervasives.Mkdtuple4
                            (g1, nts, remaining_ctxt, k_frame) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.fst"
                                          (Prims.of_int (239))
                                          (Prims.of_int (4))
                                          (Prims.of_int (239))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.fst"
                                          (Prims.of_int (241))
                                          (Prims.of_int (82))
                                          (Prims.of_int (270))
                                          (Prims.of_int (27)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       Pulse_Prover_Common.st_typing_weakening
                                         g uvs t c d g1))
                                 (fun uu___1 ->
                                    (fun d1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Prover.fst"
                                                     (Prims.of_int (242))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (242))
                                                     (Prims.of_int (35)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Prover.fst"
                                                     (Prims.of_int (242))
                                                     (Prims.of_int (38))
                                                     (Prims.of_int (270))
                                                     (Prims.of_int (27)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  Pulse_Prover_Substs.nt_subst_st_term
                                                    t nts))
                                            (fun uu___1 ->
                                               (fun t1 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Prover.fst"
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (32)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Prover.fst"
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (35))
                                                                (Prims.of_int (270))
                                                                (Prims.of_int (27)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             Pulse_Prover_Substs.nt_subst_comp
                                                               c nts))
                                                       (fun uu___1 ->
                                                          (fun c1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (47)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Prover_Substs.st_typing_nt_substs_derived
                                                                    g1 uvs t
                                                                    c d1 nts))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun d2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    coerce_eq
                                                                    k_frame
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_frame1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    ty))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1)
                                                                    (Pulse_Syntax_Base.ppname_default,
                                                                    x))
                                                                    remaining_ctxt))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    ctxt' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Prover_Common.st_typing_weakening_standard
                                                                    g1 t1 c1
                                                                    d2 g1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun d3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.continuation_elaborator_with_bind
                                                                    g1
                                                                    remaining_ctxt
                                                                    c1 t1 d3
                                                                    () x))
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    ctxt',
                                                                    g2,
                                                                    (Pulse_Checker_Common.k_elab_trans
                                                                    g g1 g2
                                                                    ctxt
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)
                                                                    remaining_ctxt)
                                                                    ctxt'
                                                                    k_frame1
                                                                    (Pulse_Checker_Common.k_elab_equiv
                                                                    g1 g2
                                                                    (Pulse_Prover_Common.op_Star
                                                                    remaining_ctxt
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1))
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)
                                                                    remaining_ctxt)
                                                                    ctxt'
                                                                    ctxt' k
                                                                    () ())))))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                            uu___1))) uu___1)))
                                      uu___1))) uu___)
let (try_frame_pre :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun t ->
          fun c ->
            fun d ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (278)) (Prims.of_int (12))
                         (Prims.of_int (278)) (Prims.of_int (32)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (280)) (Prims.of_int (2))
                         (Prims.of_int (280)) (Prims.of_int (37)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g)))
                (fun uu___ ->
                   (fun uvs ->
                      Obj.magic (try_frame_pre_uvs g ctxt () uvs t c d))
                     uu___)
let (repack :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit, unit) Pulse_Checker_Common.checker_result_t ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.range ->
            ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun ctxt ->
                 fun r ->
                   fun post_hint ->
                     fun rng ->
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
                                            "Pulse.Prover.fst"
                                            (Prims.of_int (292))
                                            (Prims.of_int (36))
                                            (Prims.of_int (292))
                                            (Prims.of_int (37)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Prover.fst"
                                            (Prims.of_int (291))
                                            (Prims.of_int (21))
                                            (Prims.of_int (316))
                                            (Prims.of_int (64)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ -> r))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         match uu___ with
                                         | FStar_Pervasives.Mkdtuple5
                                             (x, ty, ctxt', g2, k) ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.fst"
                                                           (Prims.of_int (294))
                                                           (Prims.of_int (27))
                                                           (Prims.of_int (294))
                                                           (Prims.of_int (74)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.fst"
                                                           (Prims.of_int (297))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (316))
                                                           (Prims.of_int (64)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        Pulse_Syntax_Naming.open_term_nv
                                                          post_hint1.Pulse_Typing.post
                                                          (Pulse_Syntax_Base.ppname_default,
                                                            x)))
                                                  (fun uu___1 ->
                                                     (fun post_hint_opened ->
                                                        if
                                                          Prims.op_Negation
                                                            (Pulse_Syntax_Base.eq_tm
                                                               ty
                                                               post_hint1.Pulse_Typing.ret_ty)
                                                        then
                                                          Obj.magic
                                                            (Obj.repr
                                                               (Pulse_Typing_Env.fail
                                                                  g
                                                                  (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                  "result type is not the same in stapp"))
                                                        else
                                                          Obj.magic
                                                            (Obj.repr
                                                               (if
                                                                  Pulse_Syntax_Base.eq_tm
                                                                    post_hint_opened
                                                                    ctxt'
                                                                then
                                                                  Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    post_hint_opened,
                                                                    g2, k)))
                                                                else
                                                                  Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (64)))))
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
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g3, nts,
                                                                    remaining_ctxt,
                                                                    k_post)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    coerce_eq
                                                                    k_post ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    k_post1
                                                                    ->
                                                                    match 
                                                                    Pulse_Checker_Common.check_equiv_emp
                                                                    g3
                                                                    remaining_ctxt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)
                                                                    "cannot match post hint in st app"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    post_hint_opened,
                                                                    g3,
                                                                    (Pulse_Checker_Common.k_elab_trans
                                                                    g g2 g3
                                                                    ctxt
                                                                    ctxt'
                                                                    post_hint_opened
                                                                    k
                                                                    (Pulse_Checker_Common.k_elab_equiv
                                                                    g2 g3
                                                                    ctxt'
                                                                    ctxt'
                                                                    (Pulse_Prover_Common.op_Star
                                                                    post_hint_opened
                                                                    remaining_ctxt)
                                                                    post_hint_opened
                                                                    k_post1
                                                                    () ())))))))
                                                                    uu___4)))
                                                                    uu___3)))))
                                                       uu___1))) uu___))))
              uu___4 uu___3 uu___2 uu___1 uu___