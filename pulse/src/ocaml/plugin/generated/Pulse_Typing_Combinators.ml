open Prims
let (st_comp_with_pre :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_comp)
  =
  fun st ->
    fun pre ->
      {
        Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
        Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
        Pulse_Syntax_Base.pre = pre;
        Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
      }
let (nvar_as_binder :
  Pulse_Syntax_Base.nvar ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.binder)
  =
  fun x ->
    fun t ->
      Pulse_Syntax_Base.mk_binder_ppname t (FStar_Pervasives_Native.fst x)
let (st_ghost_as_atomic :
  Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp) =
  fun c ->
    Pulse_Syntax_Base.C_STAtomic
      ((Pulse_Syntax_Base.comp_inames c), Pulse_Syntax_Base.Neutral,
        (Pulse_Syntax_Base.st_comp_of_comp c))
type ('caseuc1, 'caseuc2) bind_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            Pulse_Syntax_Base.comp_st ->
              Pulse_Syntax_Base.nvar ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  unit ->
                    (unit, unit, unit) Pulse_Typing.st_typing ->
                      unit ->
                        unit ->
                          unit Pulse_Typing.post_hint_opt ->
                            ((Pulse_Syntax_Base.st_term,
                               Pulse_Syntax_Base.comp_st,
                               (unit, unit, unit) Pulse_Typing.st_typing)
                               FStar_Pervasives.dtuple3,
                              unit) FStar_Tactics_Effect.tac_repr
let (mk_bind_st_st : (unit, unit) bind_t) =
  fun g ->
    fun pre ->
      fun e1 ->
        fun e2 ->
          fun c1 ->
            fun c2 ->
              fun px ->
                fun d_e1 ->
                  fun d_c1res ->
                    fun d_e2 ->
                      fun res_typing ->
                        fun post_typing ->
                          fun uu___ ->
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    match px with
                                    | (uu___2, x) ->
                                        FStar_Pervasives.Mkdtuple3
                                          ((Pulse_Typing.wrst
                                              (Pulse_Typing.bind_comp_out c1
                                                 c2)
                                              (Pulse_Syntax_Base.Tm_Bind
                                                 {
                                                   Pulse_Syntax_Base.binder =
                                                     (nvar_as_binder px
                                                        (Pulse_Syntax_Base.comp_res
                                                           c1));
                                                   Pulse_Syntax_Base.head1 =
                                                     e1;
                                                   Pulse_Syntax_Base.body1 =
                                                     e2
                                                 })),
                                            (Pulse_Typing.bind_comp_out c1 c2),
                                            (Pulse_Typing.T_Bind
                                               (g, e1, e2, c1, c2,
                                                 (nvar_as_binder px
                                                    (Pulse_Syntax_Base.comp_res
                                                       c1)),
                                                 (FStar_Pervasives_Native.snd
                                                    px),
                                                 (Pulse_Typing.bind_comp_out
                                                    c1 c2), d_e1, (), d_e2,
                                                 (Pulse_Typing.Bind_comp
                                                    (g, x, c1, c2, (), x, ())))))))
let (inames_of : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.term) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_ST uu___ -> Pulse_Syntax_Pure.tm_emp_inames
    | Pulse_Syntax_Base.C_STGhost (inames, uu___) -> inames
    | Pulse_Syntax_Base.C_STAtomic (inames, uu___, uu___1) -> inames
let (with_inames :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun i ->
      match c with
      | Pulse_Syntax_Base.C_ST uu___ -> c
      | Pulse_Syntax_Base.C_STGhost (uu___, sc) ->
          Pulse_Syntax_Base.C_STGhost (i, sc)
      | Pulse_Syntax_Base.C_STAtomic (uu___, obs, sc) ->
          Pulse_Syntax_Base.C_STAtomic (i, obs, sc)
let (weaken_comp_inames :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            ((Pulse_Syntax_Base.comp_st,
               (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun e ->
                 fun c ->
                   fun d_e ->
                     fun new_inames ->
                       match c with
                       | Pulse_Syntax_Base.C_ST uu___ ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> Prims.Mkdtuple2 (c, d_e))))
                       | Pulse_Syntax_Base.C_STGhost (inames, sc) ->
                           Obj.magic
                             (Obj.repr
                                (let uu___ =
                                   let uu___1 =
                                     let uu___2 =
                                       Pulse_Checker_Pure.check_prop_validity
                                         g
                                         (Pulse_Typing.tm_inames_subset
                                            inames new_inames) () in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Typing.Combinators.fst"
                                                (Prims.of_int (201))
                                                (Prims.of_int (72))
                                                (Prims.of_int (201))
                                                (Prims.of_int (129)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Typing.Combinators.fst"
                                                (Prims.of_int (201))
                                                (Prims.of_int (34))
                                                (Prims.of_int (201))
                                                (Prims.of_int (130)))))
                                       (Obj.magic uu___2)
                                       (fun uu___3 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               Pulse_Typing.STS_GhostInvs
                                                 (g, sc, inames, new_inames,
                                                   ()))) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Typing.Combinators.fst"
                                              (Prims.of_int (201))
                                              (Prims.of_int (34))
                                              (Prims.of_int (201))
                                              (Prims.of_int (130)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Typing.Combinators.fst"
                                              (Prims.of_int (201))
                                              (Prims.of_int (16))
                                              (Prims.of_int (201))
                                              (Prims.of_int (130)))))
                                     (Obj.magic uu___1)
                                     (fun uu___2 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             Pulse_Typing.T_Sub
                                               (g, e, c,
                                                 (Pulse_Syntax_Base.C_STGhost
                                                    (new_inames, sc)), d_e,
                                                 uu___2))) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (201))
                                            (Prims.of_int (16))
                                            (Prims.of_int (201))
                                            (Prims.of_int (130)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (202))
                                            (Prims.of_int (6))
                                            (Prims.of_int (202))
                                            (Prims.of_int (41)))))
                                   (Obj.magic uu___)
                                   (fun d_e1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           Prims.Mkdtuple2
                                             ((with_inames c new_inames),
                                               d_e1)))))
                       | Pulse_Syntax_Base.C_STAtomic (inames, obs, sc) ->
                           Obj.magic
                             (Obj.repr
                                (let uu___ =
                                   let uu___1 =
                                     let uu___2 =
                                       Pulse_Checker_Pure.check_prop_validity
                                         g
                                         (Pulse_Typing.tm_inames_subset
                                            inames new_inames) () in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Typing.Combinators.fst"
                                                (Prims.of_int (205))
                                                (Prims.of_int (81))
                                                (Prims.of_int (205))
                                                (Prims.of_int (138)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Typing.Combinators.fst"
                                                (Prims.of_int (205))
                                                (Prims.of_int (34))
                                                (Prims.of_int (205))
                                                (Prims.of_int (139)))))
                                       (Obj.magic uu___2)
                                       (fun uu___3 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               Pulse_Typing.STS_AtomicInvs
                                                 (g, sc, inames, new_inames,
                                                   obs, obs, ()))) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Typing.Combinators.fst"
                                              (Prims.of_int (205))
                                              (Prims.of_int (34))
                                              (Prims.of_int (205))
                                              (Prims.of_int (139)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Typing.Combinators.fst"
                                              (Prims.of_int (205))
                                              (Prims.of_int (16))
                                              (Prims.of_int (205))
                                              (Prims.of_int (139)))))
                                     (Obj.magic uu___1)
                                     (fun uu___2 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             Pulse_Typing.T_Sub
                                               (g, e, c,
                                                 (Pulse_Syntax_Base.C_STAtomic
                                                    (new_inames, obs, sc)),
                                                 d_e, uu___2))) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (205))
                                            (Prims.of_int (16))
                                            (Prims.of_int (205))
                                            (Prims.of_int (139)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (206))
                                            (Prims.of_int (6))
                                            (Prims.of_int (206))
                                            (Prims.of_int (41)))))
                                   (Obj.magic uu___)
                                   (fun d_e1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           Prims.Mkdtuple2
                                             ((with_inames c new_inames),
                                               d_e1)))))) uu___4 uu___3
              uu___2 uu___1 uu___
let (try_lift_ghost_atomic :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((unit, unit, unit) Pulse_Typing.st_typing
             FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun c ->
        fun d ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    let d1 =
                      Pulse_Typing_Metatheory_Base.st_typing_correctness g e
                        c d in
                    ())) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                     (Prims.of_int (211)) (Prims.of_int (26))
                     (Prims.of_int (215)) (Prims.of_int (5)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                     (Prims.of_int (216)) (Prims.of_int (4))
                     (Prims.of_int (222)) (Prims.of_int (10)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun comp_res_typing ->
                  let uu___1 =
                    Pulse_Checker_Pure.try_get_non_informative_witness g
                      (Pulse_Syntax_Base.comp_u c)
                      (Pulse_Syntax_Base.comp_res c) () in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Typing.Combinators.fst"
                                (Prims.of_int (217)) (Prims.of_int (10))
                                (Prims.of_int (217)) (Prims.of_int (83)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Typing.Combinators.fst"
                                (Prims.of_int (218)) (Prims.of_int (2))
                                (Prims.of_int (222)) (Prims.of_int (10)))))
                       (Obj.magic uu___1)
                       (fun w ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match w with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w1 ->
                                   FStar_Pervasives_Native.Some
                                     (Pulse_Typing.T_Lift
                                        (g, e, c,
                                          (Pulse_Syntax_Base.C_STAtomic
                                             ((Pulse_Syntax_Base.comp_inames
                                                 c),
                                               Pulse_Syntax_Base.Neutral,
                                               (Pulse_Syntax_Base.st_comp_of_comp
                                                  c))), d,
                                          (Pulse_Typing.Lift_Ghost_Neutral
                                             (g, c, w1)))))))) uu___1)
let (lift_ghost_atomic :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          ((unit, unit, unit) Pulse_Typing.st_typing, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun c ->
        fun d ->
          let uu___ = try_lift_ghost_atomic g e c d in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                     (Prims.of_int (226)) (Prims.of_int (10))
                     (Prims.of_int (226)) (Prims.of_int (33)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                     (Prims.of_int (227)) (Prims.of_int (2))
                     (Prims.of_int (237)) (Prims.of_int (5)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun w ->
                  match w with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (Obj.repr
                           (let uu___1 =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Pulse_Syntax_Base.comp_res c)) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (230))
                                       (Prims.of_int (12))
                                       (Prims.of_int (230))
                                       (Prims.of_int (22)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (231))
                                       (Prims.of_int (4))
                                       (Prims.of_int (235))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun t ->
                                    let uu___2 =
                                      let uu___3 =
                                        let uu___4 =
                                          let uu___5 =
                                            Pulse_PP.pp
                                              Pulse_PP.printable_term t in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Typing.Combinators.fst"
                                                     (Prims.of_int (234))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (234))
                                                     (Prims.of_int (16)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Typing.Combinators.fst"
                                                     (Prims.of_int (233))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (234))
                                                     (Prims.of_int (16)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 ->
                                                    FStar_Pprint.prefix
                                                      (Prims.of_int (2))
                                                      Prims.int_one
                                                      (Pulse_PP.text "Got:")
                                                      uu___6)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Combinators.fst"
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (234))
                                                   (Prims.of_int (16)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Combinators.fst"
                                                   (Prims.of_int (231))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (235))
                                                   (Prims.of_int (5)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 -> [uu___5])) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Typing.Combinators.fst"
                                                 (Prims.of_int (231))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (235))
                                                 (Prims.of_int (5)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Typing.Combinators.fst"
                                                 (Prims.of_int (231))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (235))
                                                 (Prims.of_int (5)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 ->
                                                (Pulse_PP.text
                                                   "Expected a term with a non-informative (e.g., erased) type.")
                                                :: uu___4)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Combinators.fst"
                                                  (Prims.of_int (231))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (235))
                                                  (Prims.of_int (5)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Combinators.fst"
                                                  (Prims.of_int (231))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (235))
                                                  (Prims.of_int (5)))))
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            (fun uu___3 ->
                                               Obj.magic
                                                 (Pulse_Typing_Env.fail_doc g
                                                    (FStar_Pervasives_Native.Some
                                                       (Pulse_RuntimeUtils.range_of_term
                                                          t)) uu___3)) uu___3)))
                                   uu___2)))
                  | FStar_Pervasives_Native.Some d1 ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> d1)))) uu___1)
let (mk_bind_ghost_ghost : (unit, unit) bind_t) =
  fun g ->
    fun pre ->
      fun e1 ->
        fun e2 ->
          fun c1 ->
            fun c2 ->
              fun px ->
                fun d_e1 ->
                  fun d_c1res ->
                    fun d_e2 ->
                      fun res_typing ->
                        fun post_typing ->
                          fun post_hint ->
                            let uu___ =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> px)) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (241))
                                       (Prims.of_int (13))
                                       (Prims.of_int (241))
                                       (Prims.of_int (15)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (240))
                                       (Prims.of_int (80))
                                       (Prims.of_int (265))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___)
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | (uu___2, x) ->
                                        let uu___3 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  nvar_as_binder px
                                                    (Pulse_Syntax_Base.comp_res
                                                       c1))) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Typing.Combinators.fst"
                                                      (Prims.of_int (242))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (242))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Typing.Combinators.fst"
                                                      (Prims.of_int (242))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (265))
                                                      (Prims.of_int (5)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                (fun b ->
                                                   let uu___4 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 -> c1)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (243))
                                                                 (Prims.of_int (30))
                                                                 (Prims.of_int (243))
                                                                 (Prims.of_int (32)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (242))
                                                                 (Prims.of_int (44))
                                                                 (Prims.of_int (265))
                                                                 (Prims.of_int (5)))))
                                                        (Obj.magic uu___4)
                                                        (fun uu___5 ->
                                                           (fun uu___5 ->
                                                              match uu___5
                                                              with
                                                              | Pulse_Syntax_Base.C_STGhost
                                                                  (inames1,
                                                                   sc1)
                                                                  ->
                                                                  let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    c2)) in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc2) ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    inames1
                                                                    inames2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2)
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1, c2,
                                                                    (), x,
                                                                    ()))))))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    post_hint
                                                                    then
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    g
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames1
                                                                    inames2)
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (128)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (129)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    (g, sc1,
                                                                    inames1,
                                                                    inames2,
                                                                    ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (129)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (129)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc1)),
                                                                    d_e1,
                                                                    uu___11))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (129)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    d_e11 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc1)) c2)
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc1)) c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc1)),
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc1)) c2),
                                                                    d_e11,
                                                                    (), d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (inames2,
                                                                    sc1)),
                                                                    c2, (),
                                                                    x, ())))))))
                                                                    else
                                                                    (let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.tm_join_inames
                                                                    inames1
                                                                    inames2)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    new_inames
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    g
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames1
                                                                    new_inames)
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (131)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (132)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    (g, sc1,
                                                                    inames1,
                                                                    new_inames,
                                                                    ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (132)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (132)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc1)),
                                                                    d_e1,
                                                                    uu___13))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (132)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames2
                                                                    new_inames)
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (131)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (132)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    sc2,
                                                                    inames2,
                                                                    new_inames,
                                                                    ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (132)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (132)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc2)),
                                                                    d_e2,
                                                                    uu___14))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (132)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    d_e21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc1))
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc2)))
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc1))
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc2))),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc1)),
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc2)), b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc1))
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc2))),
                                                                    d_e11,
                                                                    (),
                                                                    d_e21,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc1)),
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    (new_inames,
                                                                    sc2)),
                                                                    (), x,
                                                                    ())))))))))
                                                                    uu___12)))
                                                                    uu___11)))))
                                                                    uu___7)))
                                                             uu___5))) uu___4)))
                                   uu___1)
let (mk_bind_atomic_atomic : (unit, unit) bind_t) =
  fun g ->
    fun pre ->
      fun e1 ->
        fun e2 ->
          fun c1 ->
            fun c2 ->
              fun px ->
                fun d_e1 ->
                  fun d_c1res ->
                    fun d_e2 ->
                      fun res_typing ->
                        fun post_typing ->
                          fun post_hint ->
                            let uu___ =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> px)) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (270))
                                       (Prims.of_int (17))
                                       (Prims.of_int (270))
                                       (Prims.of_int (19)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (269))
                                       (Prims.of_int (82))
                                       (Prims.of_int (300))
                                       (Prims.of_int (7)))))
                              (Obj.magic uu___)
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | (uu___2, x) ->
                                        let uu___3 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  nvar_as_binder px
                                                    (Pulse_Syntax_Base.comp_res
                                                       c1))) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Typing.Combinators.fst"
                                                      (Prims.of_int (271))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (271))
                                                      (Prims.of_int (45)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Typing.Combinators.fst"
                                                      (Prims.of_int (271))
                                                      (Prims.of_int (48))
                                                      (Prims.of_int (300))
                                                      (Prims.of_int (7)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                (fun b ->
                                                   let uu___4 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 -> c1)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (272))
                                                                 (Prims.of_int (40))
                                                                 (Prims.of_int (272))
                                                                 (Prims.of_int (42)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (271))
                                                                 (Prims.of_int (48))
                                                                 (Prims.of_int (300))
                                                                 (Prims.of_int (7)))))
                                                        (Obj.magic uu___4)
                                                        (fun uu___5 ->
                                                           (fun uu___5 ->
                                                              match uu___5
                                                              with
                                                              | Pulse_Syntax_Base.C_STAtomic
                                                                  (inames1,
                                                                   obs1, sc1)
                                                                  ->
                                                                  let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    c2)) in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs2,
                                                                    sc2) ->
                                                                    if
                                                                    Pulse_Typing.at_most_one_observable
                                                                    obs1 obs2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    inames1
                                                                    inames2
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2)
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1, c2,
                                                                    (), x,
                                                                    ())))))))
                                                                    else
                                                                    Obj.repr
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    post_hint
                                                                    then
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    g
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames1
                                                                    inames2)
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (145)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (146)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, sc1,
                                                                    inames1,
                                                                    inames2,
                                                                    obs1,
                                                                    obs1, ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (146)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (146)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs1,
                                                                    sc1)),
                                                                    d_e1,
                                                                    uu___11))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (146)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    d_e11 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs1,
                                                                    sc1)) c2)
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs1,
                                                                    sc1)) c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs1,
                                                                    sc1)),
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs1,
                                                                    sc1)) c2),
                                                                    d_e11,
                                                                    (), d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames2,
                                                                    obs1,
                                                                    sc1)),
                                                                    c2, (),
                                                                    x, ())))))))
                                                                    else
                                                                    (let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.tm_join_inames
                                                                    inames1
                                                                    inames2)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    new_inames
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    g
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames1
                                                                    new_inames)
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (148)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, sc1,
                                                                    inames1,
                                                                    new_inames,
                                                                    obs1,
                                                                    obs1, ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1)),
                                                                    d_e1,
                                                                    uu___13))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames2
                                                                    new_inames)
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (148)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    sc2,
                                                                    inames2,
                                                                    new_inames,
                                                                    obs2,
                                                                    obs2, ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs2,
                                                                    sc2)),
                                                                    d_e2,
                                                                    uu___14))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    d_e21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1))
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs2,
                                                                    sc2)))
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1))
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs2,
                                                                    sc2))),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1)),
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs2,
                                                                    sc2)), b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1))
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs2,
                                                                    sc2))),
                                                                    d_e11,
                                                                    (),
                                                                    d_e21,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1)),
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs2,
                                                                    sc2)),
                                                                    (), x,
                                                                    ())))))))))
                                                                    uu___12)))
                                                                    uu___11)))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Should have been handled separately")))
                                                                    uu___7)))
                                                             uu___5))) uu___4)))
                                   uu___1)
let rec (mk_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            Pulse_Syntax_Base.comp_st ->
              Pulse_Syntax_Base.nvar ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  unit ->
                    (unit, unit, unit) Pulse_Typing.st_typing ->
                      unit ->
                        unit ->
                          unit Pulse_Typing.post_hint_opt ->
                            ((Pulse_Syntax_Base.st_term,
                               Pulse_Syntax_Base.comp_st,
                               (unit, unit, unit) Pulse_Typing.st_typing)
                               FStar_Pervasives.dtuple3,
                              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun e1 ->
        fun e2 ->
          fun c1 ->
            fun c2 ->
              fun px ->
                fun d_e1 ->
                  fun d_c1res ->
                    fun d_e2 ->
                      fun res_typing ->
                        fun post_typing ->
                          fun post_hint ->
                            let uu___ =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> px)) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (331))
                                       (Prims.of_int (13))
                                       (Prims.of_int (331))
                                       (Prims.of_int (15)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (330))
                                       (Prims.of_int (38))
                                       (Prims.of_int (416))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___)
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | (uu___2, x) ->
                                        let uu___3 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  nvar_as_binder px
                                                    (Pulse_Syntax_Base.comp_res
                                                       c1))) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Typing.Combinators.fst"
                                                      (Prims.of_int (332))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (332))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Typing.Combinators.fst"
                                                      (Prims.of_int (332))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (416))
                                                      (Prims.of_int (5)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                (fun b ->
                                                   let uu___4 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             fun a ->
                                                               fun tag ->
                                                                 let uu___6 =
                                                                   let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.pp_effect_annot
                                                                    (Pulse_Syntax_Base.effect_annot_of_comp
                                                                    c1) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "This computation has effect: ")
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.pp_effect_annot
                                                                    (Pulse_Syntax_Base.effect_annot_of_comp
                                                                    c2) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "The continuation has effect: ")
                                                                    uu___13)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> uu___9
                                                                    ::
                                                                    uu___11))))
                                                                    uu___9) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Cannot compose computations in this ")
                                                                    (FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    tag)
                                                                    (Pulse_PP.text
                                                                    " block:")))
                                                                    :: uu___8)) in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (88)))))
                                                                   (Obj.magic
                                                                    uu___6)
                                                                   (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e1.Pulse_Syntax_Base.range1))
                                                                    uu___7))
                                                                    uu___7))) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (335))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (339))
                                                                 (Prims.of_int (88)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (341))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (416))
                                                                 (Prims.of_int (5)))))
                                                        (Obj.magic uu___4)
                                                        (fun uu___5 ->
                                                           (fun fail_bias ->
                                                              match (c1, c2)
                                                              with
                                                              | (Pulse_Syntax_Base.C_ST
                                                                 uu___5,
                                                                 Pulse_Syntax_Base.C_ST
                                                                 uu___6) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (mk_bind_st_st
                                                                    g pre e1
                                                                    e2 c1 c2
                                                                    px d_e1
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint))
                                                              | (Pulse_Syntax_Base.C_STGhost
                                                                 (uu___5,
                                                                  uu___6),
                                                                 Pulse_Syntax_Base.C_STGhost
                                                                 (uu___7,
                                                                  uu___8)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (mk_bind_ghost_ghost
                                                                    g pre e1
                                                                    e2 c1 c2
                                                                    px d_e1
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint))
                                                              | (Pulse_Syntax_Base.C_STAtomic
                                                                 (inames1,
                                                                  obs1, sc1),
                                                                 Pulse_Syntax_Base.C_STAtomic
                                                                 (inames2,
                                                                  obs2, sc2))
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (if
                                                                    Pulse_Typing.at_most_one_observable
                                                                    obs1 obs2
                                                                    then
                                                                    Obj.repr
                                                                    (mk_bind_atomic_atomic
                                                                    g pre e1
                                                                    e2 c1 c2
                                                                    px d_e1
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint)
                                                                    else
                                                                    Obj.repr
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    post_hint
                                                                    then
                                                                    Obj.repr
                                                                    (fail_bias
                                                                    ()
                                                                    "atomic")
                                                                    else
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)),
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (84)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)) c2
                                                                    px d_e11
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint))
                                                                    uu___8)))))
                                                              | (Pulse_Syntax_Base.C_STAtomic
                                                                 (inames,
                                                                  uu___5,
                                                                  uu___6),
                                                                 Pulse_Syntax_Base.C_ST
                                                                 uu___7) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)),
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)) c2
                                                                    px d_e11
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint))
                                                                    uu___9)))
                                                              | (Pulse_Syntax_Base.C_ST
                                                                 uu___5,
                                                                 Pulse_Syntax_Base.C_STAtomic
                                                                 (inames,
                                                                  uu___6,
                                                                  uu___7)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    post_hint
                                                                    then
                                                                    Obj.repr
                                                                    (fail_bias
                                                                    ()
                                                                    "atomic")
                                                                    else
                                                                    Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)),
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)), c2))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    let uu___10
                                                                    =
                                                                    mk_bind g
                                                                    pre e1 e2
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)) px
                                                                    d_e1 ()
                                                                    d_e21 ()
                                                                    ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___10))))
                                                              | (Pulse_Syntax_Base.C_STGhost
                                                                 (uu___5,
                                                                  uu___6),
                                                                 Pulse_Syntax_Base.C_STAtomic
                                                                 (uu___7,
                                                                  Pulse_Syntax_Base.Neutral,
                                                                  uu___8)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    try_lift_ghost_atomic
                                                                    g e1 c1
                                                                    d_e1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (st_ghost_as_atomic
                                                                    c1) c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()
                                                                    post_hint))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c2),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))),
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_Neutral_Ghost
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)), c2))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    let uu___12
                                                                    =
                                                                    mk_bind g
                                                                    pre e1 e2
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c2),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))) px
                                                                    d_e1 ()
                                                                    d_e21 ()
                                                                    ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___12))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = uu___11;
                                                                    Pulse_Typing.effect_annot
                                                                    =
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    uu___12;
                                                                    Pulse_Typing.effect_annot_typing
                                                                    = uu___13;
                                                                    Pulse_Typing.ret_ty
                                                                    = uu___14;
                                                                    Pulse_Typing.u
                                                                    = uu___15;
                                                                    Pulse_Typing.ty_typing
                                                                    = uu___16;
                                                                    Pulse_Typing.post
                                                                    = uu___17;
                                                                    Pulse_Typing.x
                                                                    = uu___18;
                                                                    Pulse_Typing.post_typing_src
                                                                    = uu___19;
                                                                    Pulse_Typing.post_typing
                                                                    = uu___20;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___21
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c2),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))),
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_Neutral_Ghost
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)), c2))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    let uu___22
                                                                    =
                                                                    mk_bind g
                                                                    pre e1 e2
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c2),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))) px
                                                                    d_e1 ()
                                                                    d_e21 ()
                                                                    ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___22))
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    Obj.repr
                                                                    (fail_bias
                                                                    ()
                                                                    "atomic"))))
                                                                    uu___10)))
                                                              | (Pulse_Syntax_Base.C_STAtomic
                                                                 (uu___5,
                                                                  Pulse_Syntax_Base.Neutral,
                                                                  uu___6),
                                                                 Pulse_Syntax_Base.C_STGhost
                                                                 (uu___7,
                                                                  uu___8)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = uu___9;
                                                                    Pulse_Typing.effect_annot
                                                                    =
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    uu___10;
                                                                    Pulse_Typing.effect_annot_typing
                                                                    = uu___11;
                                                                    Pulse_Typing.ret_ty
                                                                    = uu___12;
                                                                    Pulse_Typing.u
                                                                    = uu___13;
                                                                    Pulse_Typing.ty_typing
                                                                    = uu___14;
                                                                    Pulse_Typing.post
                                                                    = uu___15;
                                                                    Pulse_Typing.x
                                                                    = uu___16;
                                                                    Pulse_Typing.post_typing_src
                                                                    = uu___17;
                                                                    Pulse_Typing.post_typing
                                                                    = uu___18;_}
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c1),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))),
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_Neutral_Ghost
                                                                    (g, c1))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (84)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c1),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))) c2
                                                                    px d_e11
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint))
                                                                    uu___20)
                                                                    | 
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    try_lift_ghost_atomic
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px) c2
                                                                    d_e2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (86)))))
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
                                                                    FStar_Pervasives_Native.Some
                                                                    d_e21 ->
                                                                    let uu___12
                                                                    =
                                                                    mk_bind g
                                                                    pre e1 e2
                                                                    c1
                                                                    (st_ghost_as_atomic
                                                                    c2) px
                                                                    d_e1 ()
                                                                    d_e21 ()
                                                                    ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c1),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))),
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_Neutral_Ghost
                                                                    (g, c1))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (Pulse_Syntax_Base.C_STGhost
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c1),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))) c2
                                                                    px d_e11
                                                                    () d_e2
                                                                    () ()
                                                                    post_hint))
                                                                    uu___13)))
                                                                    uu___11)))
                                                              | (Pulse_Syntax_Base.C_STGhost
                                                                 (uu___5,
                                                                  uu___6),
                                                                 Pulse_Syntax_Base.C_ST
                                                                 uu___7) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    lift_ghost_atomic
                                                                    g e1 c1
                                                                    d_e1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (st_ghost_as_atomic
                                                                    c1) c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()
                                                                    post_hint))
                                                                    uu___9)))
                                                              | (Pulse_Syntax_Base.C_STGhost
                                                                 (uu___5,
                                                                  uu___6),
                                                                 Pulse_Syntax_Base.C_STAtomic
                                                                 (uu___7,
                                                                  uu___8,
                                                                  uu___9)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    lift_ghost_atomic
                                                                    g e1 c1
                                                                    d_e1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    (st_ghost_as_atomic
                                                                    c1) c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()
                                                                    post_hint))
                                                                    uu___11)))
                                                              | (Pulse_Syntax_Base.C_ST
                                                                 uu___5,
                                                                 Pulse_Syntax_Base.C_STGhost
                                                                 (uu___6,
                                                                  uu___7)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    post_hint
                                                                    then
                                                                    Obj.repr
                                                                    (fail_bias
                                                                    ()
                                                                    "ghost")
                                                                    else
                                                                    Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    lift_ghost_atomic
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px) c2
                                                                    d_e2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    let uu___10
                                                                    =
                                                                    mk_bind g
                                                                    pre e1 e2
                                                                    c1
                                                                    (st_ghost_as_atomic
                                                                    c2) px
                                                                    d_e1 ()
                                                                    d_e21 ()
                                                                    ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___10))))
                                                              | (Pulse_Syntax_Base.C_STAtomic
                                                                 (uu___5,
                                                                  uu___6,
                                                                  uu___7),
                                                                 Pulse_Syntax_Base.C_STGhost
                                                                 (uu___8,
                                                                  uu___9)) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    post_hint
                                                                    then
                                                                    Obj.repr
                                                                    (fail_bias
                                                                    ()
                                                                    "ghost")
                                                                    else
                                                                    Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    lift_ghost_atomic
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px) c2
                                                                    d_e2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    let uu___12
                                                                    =
                                                                    mk_bind g
                                                                    pre e1 e2
                                                                    c1
                                                                    (st_ghost_as_atomic
                                                                    c2) px
                                                                    d_e1 ()
                                                                    d_e21 ()
                                                                    ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___12)))))
                                                             uu___5))) uu___4)))
                                   uu___1)
let (bind_res_and_post_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      Pulse_Syntax_Base.var ->
        unit Pulse_Typing.post_hint_opt ->
          ((unit * unit), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c2 ->
      fun x ->
        fun post_hint ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> Pulse_Syntax_Base.st_comp_of_comp c2)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                     (Prims.of_int (420)) (Prims.of_int (13))
                     (Prims.of_int (420)) (Prims.of_int (31)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                     (Prims.of_int (421)) (Prims.of_int (4))
                     (Prims.of_int (443)) (Prims.of_int (7)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun s2 ->
                  match post_hint with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (Obj.repr
                           (let uu___1 =
                              Pulse_Checker_Pure.check_universe g
                                s2.Pulse_Syntax_Base.res in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (425))
                                       (Prims.of_int (32))
                                       (Prims.of_int (425))
                                       (Prims.of_int (55)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Combinators.fst"
                                       (Prims.of_int (422))
                                       (Prims.of_int (13))
                                       (Prims.of_int (436))
                                       (Prims.of_int (7)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun uu___2 ->
                                    match uu___2 with
                                    | Prims.Mkdtuple2 (u, res_typing) ->
                                        if
                                          Prims.op_Negation
                                            (Pulse_Syntax_Base.eq_univ u
                                               s2.Pulse_Syntax_Base.u)
                                        then
                                          Obj.magic
                                            (Pulse_Typing_Env.fail g
                                               FStar_Pervasives_Native.None
                                               "Unexpected universe for result type")
                                        else
                                          if
                                            FStar_Set.mem x
                                              (Pulse_Syntax_Naming.freevars
                                                 s2.Pulse_Syntax_Base.post)
                                          then
                                            (let uu___4 =
                                               let uu___5 =
                                                 Pulse_Syntax_Printer.term_to_string
                                                   s2.Pulse_Syntax_Base.post in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Typing.Combinators.fst"
                                                          (Prims.of_int (429))
                                                          (Prims.of_int (95))
                                                          (Prims.of_int (429))
                                                          (Prims.of_int (121)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Prims.fst"
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         Prims.strcat
                                                           (Prims.strcat
                                                              "Bound variable "
                                                              (Prims.strcat
                                                                 (Prims.string_of_int
                                                                    x)
                                                                 " escapes scope in postcondition "))
                                                           (Prims.strcat
                                                              uu___6 ""))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (429))
                                                           (Prims.of_int (23))
                                                           (Prims.of_int (429))
                                                           (Prims.of_int (122)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (429))
                                                           (Prims.of_int (11))
                                                           (Prims.of_int (429))
                                                           (Prims.of_int (122)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        Obj.magic
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             uu___5)) uu___5)))
                                          else
                                            (let uu___5 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 -> x)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (431))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (431))
                                                           (Prims.of_int (17)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (431))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (435))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun y ->
                                                        let uu___6 =
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___7 ->
                                                                  Pulse_Syntax_Naming.open_term_nv
                                                                    s2.Pulse_Syntax_Base.post
                                                                    (
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    y))) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (61)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (31)))))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                (fun
                                                                   s2_post_opened
                                                                   ->
                                                                   let uu___7
                                                                    =
                                                                    Pulse_Checker_Pure.check_slprop_with_core
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g y
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    s2.Pulse_Syntax_Base.res)
                                                                    s2_post_opened in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ((), ())))))
                                                                  uu___7)))
                                                       uu___6)))) uu___2)))
                  | FStar_Pervasives_Native.Some post ->
                      Obj.magic
                        (Obj.repr
                           (if
                              FStar_Set.mem x
                                (Pulse_Syntax_Naming.freevars
                                   s2.Pulse_Syntax_Base.post)
                            then
                              Obj.repr
                                (Pulse_Typing_Env.fail g
                                   FStar_Pervasives_Native.None
                                   "Unexpected mismatched postcondition in bind")
                            else
                              Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> ((), ())))))) uu___1)
let (add_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.slprop ->
            unit ->
              (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
                (unit, unit, unit) Pulse_Typing.st_typing)
                FStar_Pervasives.dtuple3)
  =
  fun g ->
    fun t ->
      fun c ->
        fun t_typing ->
          fun frame ->
            fun frame_typing ->
              FStar_Pervasives.Mkdtuple3
                (t, (Pulse_Typing.add_frame c frame),
                  (Pulse_Typing.T_Frame (g, t, c, frame, (), t_typing)))
type ('g, 'ctxt, 'req) frame_for_req_in_ctxt =
  (Pulse_Syntax_Base.term, unit, unit) FStar_Pervasives.dtuple3
let (frame_of :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (unit, unit, unit) frame_for_req_in_ctxt -> Pulse_Syntax_Base.term)
  =
  fun g ->
    fun ctxt ->
      fun req ->
        fun f ->
          let uu___ = f in
          match uu___ with
          | FStar_Pervasives.Mkdtuple3 (frame, uu___1, uu___2) -> frame
let (apply_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.comp ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (unit, unit, unit) frame_for_req_in_ctxt ->
                (Pulse_Syntax_Base.comp_st,
                  (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  =
  fun g ->
    fun t ->
      fun ctxt ->
        fun ctxt_typing ->
          fun c ->
            fun t_typing ->
              fun frame_t ->
                let s = Pulse_Syntax_Base.st_comp_of_comp c in
                let uu___ = frame_t in
                match uu___ with
                | FStar_Pervasives.Mkdtuple3 (frame, frame_typing, ve) ->
                    let t_typing1 =
                      Pulse_Typing.T_Frame (g, t, c, frame, (), t_typing) in
                    let c' = Pulse_Typing.add_frame c frame in
                    let c'_typing =
                      Pulse_Typing_Metatheory_Base.st_typing_correctness g t
                        (Pulse_Typing.add_frame c frame) t_typing1 in
                    let s' = Pulse_Syntax_Base.st_comp_of_comp c' in
                    let s'' =
                      {
                        Pulse_Syntax_Base.u = (s'.Pulse_Syntax_Base.u);
                        Pulse_Syntax_Base.res = (s'.Pulse_Syntax_Base.res);
                        Pulse_Syntax_Base.pre = ctxt;
                        Pulse_Syntax_Base.post = (s'.Pulse_Syntax_Base.post)
                      } in
                    let c'' = Pulse_Syntax_Base.with_st_comp c' s'' in
                    let st_typing =
                      FStar_Pervasives_Native.fst
                        (Pulse_Typing_Metatheory_Base.comp_typing_inversion g
                           (Pulse_Typing.add_frame c frame) c'_typing) in
                    let uu___1 =
                      Pulse_Typing_Metatheory_Base.st_comp_typing_inversion g
                        (Pulse_Syntax_Base.st_comp_of_comp
                           (Pulse_Typing.add_frame c frame)) st_typing in
                    (match uu___1 with
                     | FStar_Pervasives.Mkdtuple4
                         (res_typing, pre_typing, x, post_typing) ->
                         let st_equiv =
                           Pulse_Typing.ST_SLPropEquiv
                             (g, c', c'', x, (), (), (),
                               (FStar_Reflection_Typing.Rel_refl
                                  ((Pulse_Typing.elab_env g),
                                    (Pulse_Syntax_Base.comp_res c'),
                                    FStar_Reflection_Typing.R_Eq)), (), ()) in
                         let t_typing2 =
                           Pulse_Typing.T_Equiv
                             (g, t, (Pulse_Typing.add_frame c frame), c'',
                               t_typing1, st_equiv) in
                         Prims.Mkdtuple2 (c'', t_typing2))
type ('g, 'ctxt, 'postuhint) st_typing_in_ctxt =
  (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
    (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3
let (comp_for_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      unit ->
        Pulse_Typing.post_hint_t ->
          Pulse_Syntax_Base.var ->
            ((Pulse_Syntax_Base.comp_st,
               (unit, unit, unit) Pulse_Typing.comp_typing) Prims.dtuple2,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post ->
          fun x ->
            let uu___ =
              if
                FStar_Set.mem x
                  (Pulse_Syntax_Naming.freevars post.Pulse_Typing.post)
              then
                Obj.magic
                  (Obj.repr
                     (Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                        "Impossible: unexpected freevar clash in comp_for_post_hint, please file a bug-report"))
              else
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                       (Prims.of_int (491)) (Prims.of_int (2))
                       (Prims.of_int (492)) (Prims.of_int (105)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Typing.Combinators.fst"
                       (Prims.of_int (492)) (Prims.of_int (106))
                       (Prims.of_int (514)) (Prims.of_int (54)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      match post.Pulse_Typing.effect_annot with
                      | Pulse_Syntax_Base.EffectAnnotSTT ->
                          Prims.Mkdtuple2
                            ((Pulse_Syntax_Base.C_ST
                                {
                                  Pulse_Syntax_Base.u = (post.Pulse_Typing.u);
                                  Pulse_Syntax_Base.res =
                                    (post.Pulse_Typing.ret_ty);
                                  Pulse_Syntax_Base.pre = pre;
                                  Pulse_Syntax_Base.post =
                                    (post.Pulse_Typing.post)
                                }),
                              (Pulse_Typing.CT_ST
                                 (g,
                                   {
                                     Pulse_Syntax_Base.u =
                                       (post.Pulse_Typing.u);
                                     Pulse_Syntax_Base.res =
                                       (post.Pulse_Typing.ret_ty);
                                     Pulse_Syntax_Base.pre = pre;
                                     Pulse_Syntax_Base.post =
                                       (post.Pulse_Typing.post)
                                   },
                                   (Pulse_Typing.STC
                                      (g,
                                        {
                                          Pulse_Syntax_Base.u =
                                            (post.Pulse_Typing.u);
                                          Pulse_Syntax_Base.res =
                                            (post.Pulse_Typing.ret_ty);
                                          Pulse_Syntax_Base.pre = pre;
                                          Pulse_Syntax_Base.post =
                                            (post.Pulse_Typing.post)
                                        }, x, (), (), ())))))
                      | Pulse_Syntax_Base.EffectAnnotGhost
                          { Pulse_Syntax_Base.opens = opens;_} ->
                          Prims.Mkdtuple2
                            ((Pulse_Syntax_Base.C_STGhost
                                (opens,
                                  {
                                    Pulse_Syntax_Base.u =
                                      (post.Pulse_Typing.u);
                                    Pulse_Syntax_Base.res =
                                      (post.Pulse_Typing.ret_ty);
                                    Pulse_Syntax_Base.pre = pre;
                                    Pulse_Syntax_Base.post =
                                      (post.Pulse_Typing.post)
                                  })),
                              (Pulse_Typing.CT_STGhost
                                 (g, opens,
                                   {
                                     Pulse_Syntax_Base.u =
                                       (post.Pulse_Typing.u);
                                     Pulse_Syntax_Base.res =
                                       (post.Pulse_Typing.ret_ty);
                                     Pulse_Syntax_Base.pre = pre;
                                     Pulse_Syntax_Base.post =
                                       (post.Pulse_Typing.post)
                                   }, (),
                                   (Pulse_Typing.STC
                                      (g,
                                        {
                                          Pulse_Syntax_Base.u =
                                            (post.Pulse_Typing.u);
                                          Pulse_Syntax_Base.res =
                                            (post.Pulse_Typing.ret_ty);
                                          Pulse_Syntax_Base.pre = pre;
                                          Pulse_Syntax_Base.post =
                                            (post.Pulse_Typing.post)
                                        }, x, (), (), ())))))
                      | Pulse_Syntax_Base.EffectAnnotAtomic
                          { Pulse_Syntax_Base.opens1 = opens;_} ->
                          Prims.Mkdtuple2
                            ((Pulse_Syntax_Base.C_STAtomic
                                (opens, Pulse_Syntax_Base.Neutral,
                                  {
                                    Pulse_Syntax_Base.u =
                                      (post.Pulse_Typing.u);
                                    Pulse_Syntax_Base.res =
                                      (post.Pulse_Typing.ret_ty);
                                    Pulse_Syntax_Base.pre = pre;
                                    Pulse_Syntax_Base.post =
                                      (post.Pulse_Typing.post)
                                  })),
                              (Pulse_Typing.CT_STAtomic
                                 (g, opens, Pulse_Syntax_Base.Neutral,
                                   {
                                     Pulse_Syntax_Base.u =
                                       (post.Pulse_Typing.u);
                                     Pulse_Syntax_Base.res =
                                       (post.Pulse_Typing.ret_ty);
                                     Pulse_Syntax_Base.pre = pre;
                                     Pulse_Syntax_Base.post =
                                       (post.Pulse_Typing.post)
                                   }, (),
                                   (Pulse_Typing.STC
                                      (g,
                                        {
                                          Pulse_Syntax_Base.u =
                                            (post.Pulse_Typing.u);
                                          Pulse_Syntax_Base.res =
                                            (post.Pulse_Typing.ret_ty);
                                          Pulse_Syntax_Base.pre = pre;
                                          Pulse_Syntax_Base.post =
                                            (post.Pulse_Typing.post)
                                        }, x, (), (), ())))))
                      | Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                          { Pulse_Syntax_Base.opens2 = opens;_} ->
                          Prims.Mkdtuple2
                            ((Pulse_Syntax_Base.C_STAtomic
                                (opens, Pulse_Syntax_Base.Neutral,
                                  {
                                    Pulse_Syntax_Base.u =
                                      (post.Pulse_Typing.u);
                                    Pulse_Syntax_Base.res =
                                      (post.Pulse_Typing.ret_ty);
                                    Pulse_Syntax_Base.pre = pre;
                                    Pulse_Syntax_Base.post =
                                      (post.Pulse_Typing.post)
                                  })),
                              (Pulse_Typing.CT_STAtomic
                                 (g, opens, Pulse_Syntax_Base.Neutral,
                                   {
                                     Pulse_Syntax_Base.u =
                                       (post.Pulse_Typing.u);
                                     Pulse_Syntax_Base.res =
                                       (post.Pulse_Typing.ret_ty);
                                     Pulse_Syntax_Base.pre = pre;
                                     Pulse_Syntax_Base.post =
                                       (post.Pulse_Typing.post)
                                   }, (),
                                   (Pulse_Typing.STC
                                      (g,
                                        {
                                          Pulse_Syntax_Base.u =
                                            (post.Pulse_Typing.u);
                                          Pulse_Syntax_Base.res =
                                            (post.Pulse_Typing.ret_ty);
                                          Pulse_Syntax_Base.pre = pre;
                                          Pulse_Syntax_Base.post =
                                            (post.Pulse_Typing.post)
                                        }, x, (), (), ())))))))