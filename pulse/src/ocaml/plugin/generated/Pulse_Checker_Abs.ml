open Prims
let (check_effect_annotation :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.comp -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun r ->
               fun c_annot ->
                 fun c_computed ->
                   match (c_annot, c_computed) with
                   | (Pulse_Syntax_Base.C_Tot uu___, Pulse_Syntax_Base.C_Tot
                      uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> ())))
                   | (Pulse_Syntax_Base.C_ST uu___, Pulse_Syntax_Base.C_ST
                      uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> ())))
                   | (Pulse_Syntax_Base.C_STAtomic (i, uu___),
                      Pulse_Syntax_Base.C_STAtomic (j, uu___1)) ->
                       Obj.magic
                         (Obj.repr
                            (if Pulse_Syntax_Base.eq_tm i j
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> ()))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (23))
                                             (Prims.of_int (16))
                                             (Prims.of_int (25))
                                             (Prims.of_int (39)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (22))
                                             (Prims.of_int (9))
                                             (Prims.of_int (25))
                                             (Prims.of_int (39)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (39)))))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                j))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (25))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (25))
                                                              (Prims.of_int (39)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (38)))))
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
                                                                 i))
                                                           (fun uu___4 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Annotated effect expects only invariants in "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " to be opened; but computed effect claims that invariants "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are opened")))))
                                                     (fun uu___4 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             uu___4 uu___3))))
                                               uu___3)))
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          Obj.magic
                                            (Pulse_Typing_Env.fail g
                                               (FStar_Pervasives_Native.Some
                                                  (i.Pulse_Syntax_Base.range1))
                                               uu___3)) uu___3))))
                   | (Pulse_Syntax_Base.C_STGhost (i, uu___),
                      Pulse_Syntax_Base.C_STGhost (j, uu___1)) ->
                       Obj.magic
                         (Obj.repr
                            (if Pulse_Syntax_Base.eq_tm i j
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> ()))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (23))
                                             (Prims.of_int (16))
                                             (Prims.of_int (25))
                                             (Prims.of_int (39)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (22))
                                             (Prims.of_int (9))
                                             (Prims.of_int (25))
                                             (Prims.of_int (39)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (39)))))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                j))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (25))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (25))
                                                              (Prims.of_int (39)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (38)))))
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
                                                                 i))
                                                           (fun uu___4 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Annotated effect expects only invariants in "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " to be opened; but computed effect claims that invariants "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are opened")))))
                                                     (fun uu___4 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             uu___4 uu___3))))
                                               uu___3)))
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          Obj.magic
                                            (Pulse_Typing_Env.fail g
                                               (FStar_Pervasives_Native.Some
                                                  (i.Pulse_Syntax_Base.range1))
                                               uu___3)) uu___3))))
                   | (uu___, uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Abs.fst"
                                        (Prims.of_int (28))
                                        (Prims.of_int (11))
                                        (Prims.of_int (30))
                                        (Prims.of_int (45)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Abs.fst"
                                        (Prims.of_int (27))
                                        (Prims.of_int (4))
                                        (Prims.of_int (30))
                                        (Prims.of_int (45)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (30))
                                              (Prims.of_int (18))
                                              (Prims.of_int (30))
                                              (Prims.of_int (44)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (28))
                                              (Prims.of_int (11))
                                              (Prims.of_int (30))
                                              (Prims.of_int (45)))))
                                     (Obj.magic
                                        (Pulse_Syntax_Printer.tag_of_comp
                                           c_computed))
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Abs.fst"
                                                         (Prims.of_int (28))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (45)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Abs.fst"
                                                         (Prims.of_int (28))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (45)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Abs.fst"
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Printf.fst"
                                                               (Prims.of_int (121))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (123))
                                                               (Prims.of_int (44)))))
                                                      (Obj.magic
                                                         (Pulse_Syntax_Printer.tag_of_comp
                                                            c_annot))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              fun x ->
                                                                Prims.strcat
                                                                  (Prims.strcat
                                                                    "Expected effect "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " but this function body has effect "))
                                                                  (Prims.strcat
                                                                    x "")))))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        uu___3 uu___2))))
                                          uu___2)))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     Obj.magic
                                       (Pulse_Typing_Env.fail g
                                          (FStar_Pervasives_Native.Some r)
                                          uu___2)) uu___2)))) uu___3 uu___2
            uu___1 uu___
let (check_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            Prims.bool ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit, unit)
                   Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun frame_pre ->
              fun check ->
                if FStar_Pervasives_Native.uu___is_Some post_hint
                then
                  Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                    "Unexpected post-condition annotation from context for an abstraction"
                else
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                             (Prims.of_int (44)) (Prims.of_int (14))
                             (Prims.of_int (44)) (Prims.of_int (21)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                             (Prims.of_int (45)) (Prims.of_int (2))
                             (Prims.of_int (89)) (Prims.of_int (27)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> t.Pulse_Syntax_Base.range2))
                    (fun uu___1 ->
                       (fun range ->
                          match t.Pulse_Syntax_Base.term1 with
                          | Pulse_Syntax_Base.Tm_Abs
                              {
                                Pulse_Syntax_Base.b =
                                  { Pulse_Syntax_Base.binder_ty = t1;
                                    Pulse_Syntax_Base.binder_ppname = ppname;_};
                                Pulse_Syntax_Base.q = qual;
                                Pulse_Syntax_Base.ascription = c;
                                Pulse_Syntax_Base.body = body;_}
                              ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Abs.fst"
                                            (Prims.of_int (48))
                                            (Prims.of_int (24))
                                            (Prims.of_int (48))
                                            (Prims.of_int (38)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Abs.fst"
                                            (Prims.of_int (46))
                                            (Prims.of_int (84))
                                            (Prims.of_int (89))
                                            (Prims.of_int (27)))))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_term g t1))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | FStar_Pervasives.Mkdtuple3
                                             (t2, uu___2, uu___3) ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Abs.fst"
                                                           (Prims.of_int (49))
                                                           (Prims.of_int (28))
                                                           (Prims.of_int (49))
                                                           (Prims.of_int (46)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Abs.fst"
                                                           (Prims.of_int (48))
                                                           (Prims.of_int (41))
                                                           (Prims.of_int (89))
                                                           (Prims.of_int (27)))))
                                                  (Obj.magic
                                                     (Pulse_Checker_Pure.check_universe
                                                        g t2))
                                                  (fun uu___4 ->
                                                     (fun uu___4 ->
                                                        match uu___4 with
                                                        | Prims.Mkdtuple2
                                                            (u, t_typing) ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (19)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (ppname,
                                                                    x)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun var
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    ppname t2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match c
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___6;_}
                                                                    ->
                                                                    (Pulse_Syntax_Base.tm_emp,
                                                                    FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    ty ->
                                                                    (Pulse_Syntax_Base.tm_emp,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    ty px)),
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___6 ->
                                                                    ((Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c) px),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c) px)),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) var
                                                                    Prims.int_one)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (pre_opened,
                                                                    ret_ty,
                                                                    post_hint_body)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    g'
                                                                    pre_opened))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (pre_opened1,
                                                                    pre_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    pre_opened1
                                                                    x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun pre1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (match post_hint_body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "post_hint_typing"
                                                                    range g')
                                                                    ret_ty
                                                                    post))
                                                                    (fun
                                                                    post_hint_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    post_hint_typing)))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (114)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)
                                                                    pre_opened1
                                                                    () post
                                                                    frame_pre))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body',
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (check_effect_annotation
                                                                    g'
                                                                    body'.Pulse_Syntax_Base.range2
                                                                    c c_body))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x);
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body' x)
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    }, u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body' x),
                                                                    c_body,
                                                                    (),
                                                                    body_typing)))))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                       uu___4))) uu___1)))
                         uu___1)