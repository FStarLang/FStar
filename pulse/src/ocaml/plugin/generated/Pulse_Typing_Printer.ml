open Prims
let rec (print_st_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun t ->
               fun c ->
                 fun d ->
                   match d with
                   | Pulse_Typing.T_Abs
                       (g1, x, q, b, u, body, c1, tt, body_typing) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ =
                               print_st_typing
                                 (Pulse_Typing_Env.push_binding g1 x
                                    Pulse_Syntax_Base.ppname_default
                                    b.Pulse_Syntax_Base.binder_ty)
                                 (Pulse_Syntax_Naming.open_st_term_nv body
                                    ((b.Pulse_Syntax_Base.binder_ppname), x))
                                 c1 body_typing in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (28))
                                        (Prims.of_int (38))
                                        (Prims.of_int (28))
                                        (Prims.of_int (67)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       Prims.strcat "(T_Abs ... "
                                         (Prims.strcat uu___1 ")")))))
                   | Pulse_Typing.T_STApp
                       (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                        uu___6, uu___7)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___8 -> "T_STApp")))
                   | Pulse_Typing.T_Return
                       (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                        uu___6, uu___7, uu___8, uu___9, uu___10)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___11 -> "T_Return")))
                   | Pulse_Typing.T_Lift
                       (uu___, uu___1, uu___2, uu___3, d1, uu___4) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___5 =
                               print_st_typing uu___ uu___1 uu___2 d1 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (37))
                                        (Prims.of_int (35))
                                        (Prims.of_int (37))
                                        (Prims.of_int (54)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 ->
                                       Prims.strcat "(T_Lift "
                                         (Prims.strcat uu___6 ")")))))
                   | Pulse_Typing.T_Bind
                       (g1, e1, e2, c1, c2, b, x, c3, d1, uu___, d2, uu___1)
                       ->
                       Obj.magic
                         (Obj.repr
                            (let uu___2 =
                               print_st_typing
                                 (Pulse_Typing_Env.push_binding g1 x
                                    Pulse_Syntax_Base.ppname_default
                                    (Pulse_Syntax_Base.comp_res c1))
                                 (Pulse_Syntax_Naming.open_st_term_nv e2
                                    ((b.Pulse_Syntax_Base.binder_ppname), x))
                                 c2 d2 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (40))
                                        (Prims.of_int (59))
                                        (Prims.of_int (40))
                                        (Prims.of_int (79)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (40))
                                        (Prims.of_int (6))
                                        (Prims.of_int (40))
                                        (Prims.of_int (79)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     let uu___4 =
                                       let uu___5 =
                                         print_st_typing g1 e1 c1 d1 in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Printer.fst"
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (38))
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (58)))))
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
                                                 fun x1 ->
                                                   Prims.strcat
                                                     (Prims.strcat "(T_Bind "
                                                        (Prims.strcat uu___6
                                                           " "))
                                                     (Prims.strcat x1 ")"))) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Printer.fst"
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (79)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Printer.fst"
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (79)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 -> uu___5 uu___3))))
                                    uu___3)))
                   | Pulse_Typing.T_Frame (g1, e, c1, frame, uu___, body) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___1 = print_st_typing g1 e c1 body in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (43))
                                        (Prims.of_int (83))
                                        (Prims.of_int (43))
                                        (Prims.of_int (105)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (43))
                                        (Prims.of_int (6))
                                        (Prims.of_int (43))
                                        (Prims.of_int (105)))))
                               (Obj.magic uu___1)
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     let uu___3 =
                                       let uu___4 =
                                         Pulse_Syntax_Printer.term_to_string
                                           frame in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Printer.fst"
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (39))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (82)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Printf.fst"
                                                  (Prims.of_int (122))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (124))
                                                  (Prims.of_int (44)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 fun x ->
                                                   Prims.strcat
                                                     (Prims.strcat
                                                        "(T_Frame "
                                                        (Prims.strcat uu___5
                                                           " "))
                                                     (Prims.strcat x ")"))) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Printer.fst"
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (105)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Printer.fst"
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (105)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 -> uu___4 uu___2))))
                                    uu___2)))
                   | Pulse_Typing.T_If
                       (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                        uu___6, uu___7, uu___8, uu___9)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___10 -> "T_If")))
                   | Pulse_Typing.T_Match
                       (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                        uu___6, uu___7, uu___8, uu___9, uu___10)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___11 -> "T_Match")))
                   | Pulse_Typing.T_Equiv (g1, e, c1, c', d1, eq) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ = print_st_typing g1 e c1 d1 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Printer.fst"
                                        (Prims.of_int (53))
                                        (Prims.of_int (9))
                                        (Prims.of_int (53))
                                        (Prims.of_int (28)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       Prims.strcat "(T_Equiv "
                                         (Prims.strcat uu___1 ")")))))
                   | Pulse_Typing.T_IntroPure (uu___, uu___1, uu___2, uu___3)
                       ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 -> "T_IntroPure")))
                   | Pulse_Typing.T_Rewrite
                       (uu___, uu___1, uu___2, uu___3, uu___4) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> "T_Rewrite")))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> "<UNK>")))) uu___3 uu___2
            uu___1 uu___