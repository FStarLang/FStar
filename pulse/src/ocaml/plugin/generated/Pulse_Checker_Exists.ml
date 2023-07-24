open Prims

let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
               (Prims.of_int (28)) (Prims.of_int (23)) (Prims.of_int (28))
               (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
               (Prims.of_int (28)) (Prims.of_int (4)) (Prims.of_int (28))
               (Prims.of_int (68)))))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (check_elim_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                       (Prims.of_int (38)) (Prims.of_int (32))
                       (Prims.of_int (38)) (Prims.of_int (38)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                       (Prims.of_int (36)) (Prims.of_int (46))
                       (Prims.of_int (69)) (Prims.of_int (60)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> t.Pulse_Syntax_Base.term1))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | Pulse_Syntax_Base.Tm_ElimExists
                        { Pulse_Syntax_Base.p1 = t1;_} ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Exists.fst"
                                      (Prims.of_int (40)) (Prims.of_int (4))
                                      (Prims.of_int (56)) (Prims.of_int (21)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Exists.fst"
                                      (Prims.of_int (38)) (Prims.of_int (41))
                                      (Prims.of_int (69)) (Prims.of_int (60)))))
                             (match t1.Pulse_Syntax_Base.t with
                              | Pulse_Syntax_Base.Tm_Unknown ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Exists.fst"
                                                (Prims.of_int (43))
                                                (Prims.of_int (15))
                                                (Prims.of_int (43))
                                                (Prims.of_int (32)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Exists.fst"
                                                (Prims.of_int (43))
                                                (Prims.of_int (35))
                                                (Prims.of_int (52))
                                                (Prims.of_int (41)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             Pulse_Typing_Combinators.vprop_as_list
                                               pre))
                                       (fun uu___1 ->
                                          (fun ts ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Exists.fst"
                                                           (Prims.of_int (44))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (44))
                                                           (Prims.of_int (110)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Exists.fst"
                                                           (Prims.of_int (45))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (52))
                                                           (Prims.of_int (41)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        FStar_List_Tot_Base.filter
                                                          (fun uu___2 ->
                                                             match uu___2
                                                             with
                                                             | {
                                                                 Pulse_Syntax_Base.t
                                                                   =
                                                                   Pulse_Syntax_Base.Tm_ExistsSL
                                                                   (uu___3,
                                                                    uu___4,
                                                                    uu___5);
                                                                 Pulse_Syntax_Base.range1
                                                                   = uu___6;_}
                                                                 -> true
                                                             | uu___3 ->
                                                                 false) ts))
                                                  (fun uu___1 ->
                                                     (fun exist_tms ->
                                                        match exist_tms with
                                                        | one::[] ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    Prims.Mkdtuple2
                                                                    (one, ()))))
                                                        | uu___1 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    exist_tms))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Could not decide which exists term to eliminate: choices are\n"
                                                                    (Prims.strcat
                                                                    uu___2 "")))))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    uu___2))
                                                                    uu___2))))
                                                       uu___1))) uu___1))
                              | uu___1 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Exists.fst"
                                                (Prims.of_int (55))
                                                (Prims.of_int (17))
                                                (Prims.of_int (55))
                                                (Prims.of_int (47)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Exists.fst"
                                                (Prims.of_int (54))
                                                (Prims.of_int (10))
                                                (Prims.of_int (56))
                                                (Prims.of_int (21)))))
                                       (Obj.magic
                                          (Pulse_Checker_Pure.instantiate_term_implicits
                                             g t1))
                                       (fun uu___2 ->
                                          (fun uu___2 ->
                                             match uu___2 with
                                             | (t2, uu___3) ->
                                                 Obj.magic
                                                   (Pulse_Checker_Pure.check_vprop
                                                      g t2)) uu___2)))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | Prims.Mkdtuple2 (t2, t_typing) ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Exists.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (60)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Exists.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (60)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> uu___1))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Exists.fst"
                                                                (Prims.of_int (59))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (60))
                                                                (Prims.of_int (59)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Exists.fst"
                                                                (Prims.of_int (60))
                                                                (Prims.of_int (60))
                                                                (Prims.of_int (69))
                                                                (Prims.of_int (60)))))
                                                       (if
                                                          Prims.op_Negation
                                                            (Pulse_Syntax_Base.uu___is_Tm_ExistsSL
                                                               t2.Pulse_Syntax_Base.t)
                                                        then
                                                          Obj.magic
                                                            (Obj.repr
                                                               (Pulse_Typing_Env.fail
                                                                  g
                                                                  FStar_Pervasives_Native.None
                                                                  "elim_exists argument not a Tm_ExistsSL"))
                                                        else
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    -> ()))))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (44)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (60)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    t2.Pulse_Syntax_Base.t))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = ty;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = uu___5;_},
                                                                    p) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u',
                                                                    ty_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_univ
                                                                    u u'
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_ElimExists
                                                                    (g, u,
                                                                    ty, p, x,
                                                                    (), ())))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.try_frame_pre
                                                                    g pre ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_ElimExists
                                                                    {
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u
                                                                    (Pulse_Typing.as_binder
                                                                    ty) p)
                                                                    }))
                                                                    (Pulse_Typing.comp_elim_exists
                                                                    u ty p
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)) d))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Prover.repack
                                                                    g pre
                                                                    uu___7
                                                                    post_hint
                                                                    t2.Pulse_Syntax_Base.range1))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Universe checking failed in elim_exists"))
                                                                    uu___6)))
                                                                    uu___4)))
                                                            uu___3))) uu___2)))
                                  uu___1))) uu___)
let (intro_exists_witness_singleton :
  Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = uu___; Pulse_Syntax_Base.p2 = uu___1;
          Pulse_Syntax_Base.witnesses = uu___2::[];_}
        -> true
    | uu___ -> false
let (intro_exists_vprop :
  Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.vprop) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = uu___; Pulse_Syntax_Base.p2 = p;
          Pulse_Syntax_Base.witnesses = uu___1;_}
        -> p
let (is_intro_exists_erased : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = erased; Pulse_Syntax_Base.p2 = uu___;
          Pulse_Syntax_Base.witnesses = uu___1;_}
        -> erased
    | uu___ -> false
let (check_intro_exists_erased :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      unit FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun vprop_typing ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                         (Prims.of_int (86)) (Prims.of_int (46))
                         (Prims.of_int (86)) (Prims.of_int (53)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                         (Prims.of_int (84)) (Prims.of_int (46))
                         (Prims.of_int (103)) (Prims.of_int (65)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_IntroExists
                          { Pulse_Syntax_Base.erased = uu___1;
                            Pulse_Syntax_Base.p2 = t;
                            Pulse_Syntax_Base.witnesses = e::[];_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Exists.fst"
                                        (Prims.of_int (88))
                                        (Prims.of_int (4))
                                        (Prims.of_int (90))
                                        (Prims.of_int (26)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Exists.fst"
                                        (Prims.of_int (86))
                                        (Prims.of_int (56))
                                        (Prims.of_int (103))
                                        (Prims.of_int (65)))))
                               (match vprop_typing with
                                | FStar_Pervasives_Native.Some typing ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               Prims.Mkdtuple2 (t, ()))))
                                | uu___2 ->
                                    Obj.magic
                                      (Obj.repr
                                         (Pulse_Checker_Pure.check_vprop g t)))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | Prims.Mkdtuple2 (t1, t_typing) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Exists.fst"
                                                       (Prims.of_int (93))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (94))
                                                       (Prims.of_int (59)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Exists.fst"
                                                       (Prims.of_int (94))
                                                       (Prims.of_int (60))
                                                       (Prims.of_int (103))
                                                       (Prims.of_int (65)))))
                                              (if
                                                 Prims.op_Negation
                                                   (Pulse_Syntax_Base.uu___is_Tm_ExistsSL
                                                      t1.Pulse_Syntax_Base.t)
                                               then
                                                 Obj.magic
                                                   (Obj.repr
                                                      (Pulse_Typing_Env.fail
                                                         g
                                                         FStar_Pervasives_Native.None
                                                         "elim_exists argument not a Tm_ExistsSL"))
                                               else
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 -> ()))))
                                              (fun uu___3 ->
                                                 (fun uu___3 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Exists.fst"
                                                                  (Prims.of_int (96))
                                                                  (Prims.of_int (26))
                                                                  (Prims.of_int (96))
                                                                  (Prims.of_int (39)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Exists.fst"
                                                                  (Prims.of_int (94))
                                                                  (Prims.of_int (60))
                                                                  (Prims.of_int (103))
                                                                  (Prims.of_int (65)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               t1.Pulse_Syntax_Base.t))
                                                         (fun uu___4 ->
                                                            (fun uu___4 ->
                                                               match uu___4
                                                               with
                                                               | Pulse_Syntax_Base.Tm_ExistsSL
                                                                   (u, b, p)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Metatheory.tm_exists_inversion
                                                                    g u
                                                                    b.Pulse_Syntax_Base.binder_ty
                                                                    p ()
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (ty_typing,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g e
                                                                    (Pulse_Typing.mk_erased
                                                                    u
                                                                    b.Pulse_Syntax_Base.binder_ty)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (e1,
                                                                    e_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing.T_IntroExistsErased
                                                                    (g, u, b,
                                                                    p, e1,
                                                                    (), (),
                                                                    ())))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.try_frame_pre
                                                                    g pre ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p2
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b p);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e1]
                                                                    }))
                                                                    (Pulse_Typing.comp_intro_exists_erased
                                                                    u b p e1)
                                                                    d))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Prover.repack
                                                                    g pre
                                                                    uu___8
                                                                    post_hint
                                                                    t1.Pulse_Syntax_Base.range1))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                              uu___4)))
                                                   uu___3))) uu___2))) uu___)
let (check_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      unit FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun vprop_typing ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                         (Prims.of_int (115)) (Prims.of_int (52))
                         (Prims.of_int (115)) (Prims.of_int (59)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                         (Prims.of_int (113)) (Prims.of_int (46))
                         (Prims.of_int (133)) (Prims.of_int (65)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_IntroExists
                          { Pulse_Syntax_Base.erased = uu___1;
                            Pulse_Syntax_Base.p2 = t;
                            Pulse_Syntax_Base.witnesses = witness::[];_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Exists.fst"
                                        (Prims.of_int (117))
                                        (Prims.of_int (4))
                                        (Prims.of_int (119))
                                        (Prims.of_int (26)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Exists.fst"
                                        (Prims.of_int (115))
                                        (Prims.of_int (62))
                                        (Prims.of_int (133))
                                        (Prims.of_int (65)))))
                               (match vprop_typing with
                                | FStar_Pervasives_Native.Some typing ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               Prims.Mkdtuple2 (t, ()))))
                                | uu___2 ->
                                    Obj.magic
                                      (Obj.repr
                                         (Pulse_Checker_Pure.check_vprop g t)))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | Prims.Mkdtuple2 (t1, t_typing) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Exists.fst"
                                                       (Prims.of_int (122))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (123))
                                                       (Prims.of_int (59)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Exists.fst"
                                                       (Prims.of_int (123))
                                                       (Prims.of_int (60))
                                                       (Prims.of_int (133))
                                                       (Prims.of_int (65)))))
                                              (if
                                                 Prims.op_Negation
                                                   (Pulse_Syntax_Base.uu___is_Tm_ExistsSL
                                                      t1.Pulse_Syntax_Base.t)
                                               then
                                                 Obj.magic
                                                   (Obj.repr
                                                      (Pulse_Typing_Env.fail
                                                         g
                                                         FStar_Pervasives_Native.None
                                                         "elim_exists argument not a Tm_ExistsSL"))
                                               else
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 -> ()))))
                                              (fun uu___3 ->
                                                 (fun uu___3 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Exists.fst"
                                                                  (Prims.of_int (125))
                                                                  (Prims.of_int (26))
                                                                  (Prims.of_int (125))
                                                                  (Prims.of_int (39)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Exists.fst"
                                                                  (Prims.of_int (123))
                                                                  (Prims.of_int (60))
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (65)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               t1.Pulse_Syntax_Base.t))
                                                         (fun uu___4 ->
                                                            (fun uu___4 ->
                                                               match uu___4
                                                               with
                                                               | Pulse_Syntax_Base.Tm_ExistsSL
                                                                   (u, b, p)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Metatheory.tm_exists_inversion
                                                                    g u
                                                                    b.Pulse_Syntax_Base.binder_ty
                                                                    p ()
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (ty_typing,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g witness
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (witness1,
                                                                    witness_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing.T_IntroExists
                                                                    (g, u, b,
                                                                    p,
                                                                    witness1,
                                                                    (), (),
                                                                    ())))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Typing.comp_intro_exists
                                                                    u b p
                                                                    witness1),
                                                                    d)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c, d1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.try_frame_pre
                                                                    g pre ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p2
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b p);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    [witness1]
                                                                    })) c d1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Prover.repack
                                                                    g pre
                                                                    uu___10
                                                                    post_hint
                                                                    t1.Pulse_Syntax_Base.range1))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                              uu___4)))
                                                   uu___3))) uu___2))) uu___)
let (check_intro_exists_either :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      unit FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun vprop_typing ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              if is_intro_exists_erased st
              then
                check_intro_exists_erased g st vprop_typing pre () post_hint
              else check_intro_exists g st vprop_typing pre () post_hint