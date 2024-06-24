open Prims
let (check_effect :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option ->
              ((Pulse_Syntax_Base.ctag, Pulse_Syntax_Base.term, unit)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun e ->
                   fun eff ->
                     fun t ->
                       fun d ->
                         fun c ->
                           match (c, eff) with
                           | (FStar_Pervasives_Native.None,
                              FStar_TypeChecker_Core.E_Total) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          FStar_Pervasives.Mkdtuple3
                                            (Pulse_Syntax_Base.STT_Atomic, e,
                                              ()))))
                           | (FStar_Pervasives_Native.None,
                              FStar_TypeChecker_Core.E_Ghost) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          FStar_Pervasives.Mkdtuple3
                                            (Pulse_Syntax_Base.STT_Ghost, e,
                                              ()))))
                           | (FStar_Pervasives_Native.Some
                              (Pulse_Syntax_Base.STT_Ghost),
                              FStar_TypeChecker_Core.E_Total) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          FStar_Pervasives.Mkdtuple3
                                            (Pulse_Syntax_Base.STT_Atomic, e,
                                              ()))))
                           | (FStar_Pervasives_Native.Some
                              (Pulse_Syntax_Base.STT_Ghost),
                              FStar_TypeChecker_Core.E_Ghost) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          FStar_Pervasives.Mkdtuple3
                                            (Pulse_Syntax_Base.STT_Ghost, e,
                                              ()))))
                           | (uu___, FStar_TypeChecker_Core.E_Total) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          FStar_Pervasives.Mkdtuple3
                                            (Pulse_Syntax_Base.STT_Atomic, e,
                                              ()))))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (Pulse_Typing_Env.fail g
                                       (FStar_Pervasives_Native.Some
                                          (Pulse_RuntimeUtils.range_of_term e))
                                       "Expected a total term, but this term has Ghost effect")))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (check_tot_or_ghost_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option ->
          ((Pulse_Syntax_Base.ctag, Pulse_Syntax_Base.term, unit)
             FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        fun c ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                     (Prims.of_int (51)) (Prims.of_int (24))
                     (Prims.of_int (51)) (Prims.of_int (48)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                     (Prims.of_int (51)) Prims.int_one (Prims.of_int (52))
                     (Prims.of_int (18)))))
            (Obj.magic (Pulse_Checker_Pure.check_term_at_type g e t))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives.Mkdtuple3 (e1, eff, d) ->
                      Obj.magic (check_effect g e1 eff t () c)) uu___)
type 'g result_of_typing =
  | R of Pulse_Syntax_Base.ctag * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.universe * Pulse_Syntax_Base.term * unit * unit 
let (uu___is_R : Pulse_Typing_Env.env -> unit result_of_typing -> Prims.bool)
  = fun g -> fun projectee -> true
let (__proj__R__item__c :
  Pulse_Typing_Env.env -> unit result_of_typing -> Pulse_Syntax_Base.ctag) =
  fun g ->
    fun projectee -> match projectee with | R (c, t, u, ty, _4, _5) -> c
let (__proj__R__item__t :
  Pulse_Typing_Env.env -> unit result_of_typing -> Pulse_Syntax_Base.term) =
  fun g ->
    fun projectee -> match projectee with | R (c, t, u, ty, _4, _5) -> t
let (__proj__R__item__u :
  Pulse_Typing_Env.env -> unit result_of_typing -> Pulse_Syntax_Base.universe)
  =
  fun g ->
    fun projectee -> match projectee with | R (c, t, u, ty, _4, _5) -> u
let (__proj__R__item__ty :
  Pulse_Typing_Env.env -> unit result_of_typing -> Pulse_Syntax_Base.term) =
  fun g ->
    fun projectee -> match projectee with | R (c, t, u, ty, _4, _5) -> ty


let (compute_tot_or_ghost_term_type_and_u :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option ->
        (unit result_of_typing, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun c ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                   (Prims.of_int (67)) (Prims.of_int (41))
                   (Prims.of_int (67)) (Prims.of_int (68)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                   (Prims.of_int (67)) Prims.int_one (Prims.of_int (69))
                   (Prims.of_int (17)))))
          (Obj.magic (Pulse_Checker_Pure.compute_term_type_and_u g e))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Pervasives.Mkdtuple5
                    (t, eff, ty, Prims.Mkdtuple2 (u, ud), d) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Return.fst"
                                  (Prims.of_int (68)) (Prims.of_int (22))
                                  (Prims.of_int (68)) (Prims.of_int (38)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Return.fst"
                                  (Prims.of_int (67)) (Prims.of_int (71))
                                  (Prims.of_int (69)) (Prims.of_int (17)))))
                         (Obj.magic (check_effect g t eff ty () c))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 match uu___1 with
                                 | FStar_Pervasives.Mkdtuple3 (c1, e1, d1) ->
                                     R (c1, e1, u, ty, (), ()))))) uu___)
let (check_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun st ->
              fun ctag_ctxt ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                           (Prims.of_int (82)) (Prims.of_int (10))
                           (Prims.of_int (82)) (Prims.of_int (48)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                           (Prims.of_int (82)) (Prims.of_int (51))
                           (Prims.of_int (138)) (Prims.of_int (40)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "check_return"
                          st.Pulse_Syntax_Base.range1 g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Return.fst"
                                      (Prims.of_int (83)) (Prims.of_int (60))
                                      (Prims.of_int (83)) (Prims.of_int (67)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Return.fst"
                                      (Prims.of_int (82)) (Prims.of_int (51))
                                      (Prims.of_int (138))
                                      (Prims.of_int (40)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> st.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_Return
                                       {
                                         Pulse_Syntax_Base.expected_type =
                                           expected_type;
                                         Pulse_Syntax_Base.insert_eq = use_eq;
                                         Pulse_Syntax_Base.term = t;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Return.fst"
                                                     (Prims.of_int (86))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (98))
                                                     (Prims.of_int (27)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Return.fst"
                                                     (Prims.of_int (99))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (138))
                                                     (Prims.of_int (40)))))
                                            (match post_hint with
                                             | FStar_Pervasives_Native.Some
                                                 post ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            FStar_Pervasives_Native.Some
                                                              (FStar_Pervasives.Mkdtuple3
                                                                 ((post.Pulse_Typing.ret_ty),
                                                                   (post.Pulse_Typing.u),
                                                                   ())))))
                                             | uu___1 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (match Pulse_Syntax_Pure.inspect_term
                                                               expected_type
                                                       with
                                                       | Pulse_Syntax_Pure.Tm_Unknown
                                                           ->
                                                           Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Pervasives_Native.None))
                                                       | uu___2 ->
                                                           Obj.repr
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (81)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (27)))))
                                                                (Obj.magic
                                                                   (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g1
                                                                    expected_type))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ty,
                                                                    uu___4)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g1 ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u, d) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (ty, u,
                                                                    ()))))))
                                                                    uu___3)))))
                                            (fun uu___1 ->
                                               (fun return_type ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Return.fst"
                                                                (Prims.of_int (101))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (106))
                                                                (Prims.of_int (32)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Return.fst"
                                                                (Prims.of_int (99))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (138))
                                                                (Prims.of_int (40)))))
                                                       (match return_type
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            Obj.magic
                                                              (compute_tot_or_ghost_term_type_and_u
                                                                 g1 t
                                                                 ctag_ctxt)
                                                        | FStar_Pervasives_Native.Some
                                                            (FStar_Pervasives.Mkdtuple3
                                                            (ret_ty, u,
                                                             ty_typing))
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (70)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (32)))))
                                                                 (Obj.magic
                                                                    (
                                                                    check_tot_or_ghost_term
                                                                    g1 t
                                                                    ret_ty
                                                                    ctag_ctxt))
                                                                 (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c, t1,
                                                                    d) ->
                                                                    R
                                                                    (c, t1,
                                                                    u,
                                                                    ret_ty,
                                                                    (), ())))))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | R
                                                                 (c, t1, u,
                                                                  ty, uty, d)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (res_ppname,
                                                                    x)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_term
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) ty)
                                                                    Pulse_Syntax_Pure.tm_emp
                                                                    Pulse_Syntax_Pure.tm_vprop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (t2, ty1)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (t2, ()))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    post))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post1 ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post1.Pulse_Typing.post)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "check_return: unexpected variable clash in return post,please file a bug report"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Naming.open_term_nv
                                                                    post1.Pulse_Typing.post
                                                                    px), ())))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Return
                                                                    (g1, c,
                                                                    use_eq,
                                                                    u, ty,
                                                                    t1, post,
                                                                    x, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    c)
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.expected_type
                                                                    =
                                                                    Pulse_Syntax_Pure.tm_unknown;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    }))
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t1
                                                                    post x)
                                                                    d1
                                                                    post_hint))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun dd
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.debug
                                                                    g1
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    dd))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uu___7,
                                                                    c1,
                                                                    uu___8)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "Return comp is: "
                                                                    (Prims.strcat
                                                                    uu___9 "")))))
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
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    false g1
                                                                    ctxt ()
                                                                    dd
                                                                    res_ppname))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g1 ctxt
                                                                    uu___6
                                                                    post_hint
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t1)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                            uu___1))) uu___1)))
                                  uu___))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun st ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                           (Prims.of_int (150)) (Prims.of_int (22))
                           (Prims.of_int (150)) (Prims.of_int (29)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                           (Prims.of_int (150)) (Prims.of_int (3))
                           (Prims.of_int (166)) (Prims.of_int (5)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> st.Pulse_Syntax_Base.term1))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax_Base.Tm_Return f ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Return.fst"
                                          (Prims.of_int (151))
                                          (Prims.of_int (10))
                                          (Prims.of_int (151))
                                          (Prims.of_int (61)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Return.fst"
                                          (Prims.of_int (151))
                                          (Prims.of_int (4))
                                          (Prims.of_int (166))
                                          (Prims.of_int (5)))))
                                 (Obj.magic
                                    (Pulse_Checker_Base.is_stateful_application
                                       g f.Pulse_Syntax_Base.term))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       match uu___1 with
                                       | FStar_Pervasives_Native.Some st_app
                                           ->
                                           Obj.magic
                                             (check1 g ctxt () post_hint
                                                res_ppname st_app)
                                       | FStar_Pervasives_Native.None ->
                                           (match post_hint with
                                            | FStar_Pervasives_Native.Some p
                                                ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Return.fst"
                                                              (Prims.of_int (159))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (161))
                                                              (Prims.of_int (30)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Return.fst"
                                                              (Prims.of_int (162))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (162))
                                                              (Prims.of_int (73)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           match Pulse_Syntax_Base.ctag_of_effect_annot
                                                                   p.Pulse_Typing.effect_annot
                                                           with
                                                           | FStar_Pervasives_Native.Some
                                                               c -> c
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Pulse_Syntax_Base.STT_Atomic))
                                                     (fun uu___2 ->
                                                        (fun ctag ->
                                                           Obj.magic
                                                             (check_core g
                                                                ctxt ()
                                                                post_hint
                                                                res_ppname st
                                                                (FStar_Pervasives_Native.Some
                                                                   ctag)))
                                                          uu___2))
                                            | uu___2 ->
                                                Obj.magic
                                                  (check_core g ctxt ()
                                                     post_hint res_ppname st
                                                     FStar_Pervasives_Native.None)))
                                      uu___1))) uu___)