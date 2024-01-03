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
      {
        Pulse_Syntax_Base.binder_ty = t;
        Pulse_Syntax_Base.binder_ppname = (FStar_Pervasives_Native.fst x)
      }
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
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  match px with
                                  | (uu___1, x) ->
                                      FStar_Pervasives.Mkdtuple3
                                        ((Pulse_Typing.wr
                                            (Pulse_Typing.bind_comp_out c1 c2)
                                            (Pulse_Syntax_Base.Tm_Bind
                                               {
                                                 Pulse_Syntax_Base.binder =
                                                   (nvar_as_binder px
                                                      (Pulse_Syntax_Base.comp_res
                                                         c1));
                                                 Pulse_Syntax_Base.head1 = e1;
                                                 Pulse_Syntax_Base.body1 = e2
                                               })),
                                          (Pulse_Typing.bind_comp_out c1 c2),
                                          (Pulse_Typing.T_Bind
                                             (g, e1, e2, c1, c2,
                                               (nvar_as_binder px
                                                  (Pulse_Syntax_Base.comp_res
                                                     c1)),
                                               (FStar_Pervasives_Native.snd
                                                  px),
                                               (Pulse_Typing.bind_comp_out c1
                                                  c2), d_e1, (), d_e2,
                                               (Pulse_Typing.Bind_comp
                                                  (g, x, c1, c2, (), x, ())))))))
let (inames_of : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.term) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_ST uu___ -> Pulse_Syntax_Base.tm_emp_inames
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
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (196))
                                            (Prims.of_int (16))
                                            (Prims.of_int (196))
                                            (Prims.of_int (130)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (197))
                                            (Prims.of_int (6))
                                            (Prims.of_int (197))
                                            (Prims.of_int (41)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Combinators.fst"
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (130)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Combinators.fst"
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (130)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Typing.Combinators.fst"
                                                        (Prims.of_int (196))
                                                        (Prims.of_int (72))
                                                        (Prims.of_int (196))
                                                        (Prims.of_int (129)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Typing.Combinators.fst"
                                                        (Prims.of_int (196))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (196))
                                                        (Prims.of_int (130)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.check_prop_validity
                                                     g
                                                     (Pulse_Typing.tm_inames_subset
                                                        inames new_inames) ()))
                                               (fun uu___ ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Pulse_Typing.STS_GhostInvs
                                                         (g, sc, inames,
                                                           new_inames, ())))))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 Pulse_Typing.T_Sub
                                                   (g, e, c,
                                                     (Pulse_Syntax_Base.C_STGhost
                                                        (new_inames, sc)),
                                                     d_e, uu___)))))
                                   (fun d_e1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ ->
                                           Prims.Mkdtuple2
                                             ((with_inames c new_inames),
                                               d_e1)))))
                       | Pulse_Syntax_Base.C_STAtomic (inames, obs, sc) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (200))
                                            (Prims.of_int (16))
                                            (Prims.of_int (200))
                                            (Prims.of_int (139)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Typing.Combinators.fst"
                                            (Prims.of_int (201))
                                            (Prims.of_int (6))
                                            (Prims.of_int (201))
                                            (Prims.of_int (41)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Combinators.fst"
                                                  (Prims.of_int (200))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (200))
                                                  (Prims.of_int (139)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Typing.Combinators.fst"
                                                  (Prims.of_int (200))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (200))
                                                  (Prims.of_int (139)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Typing.Combinators.fst"
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (81))
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (138)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Typing.Combinators.fst"
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (139)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.check_prop_validity
                                                     g
                                                     (Pulse_Typing.tm_inames_subset
                                                        inames new_inames) ()))
                                               (fun uu___ ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Pulse_Typing.STS_AtomicInvs
                                                         (g, sc, inames,
                                                           new_inames, obs,
                                                           obs, ())))))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 Pulse_Typing.T_Sub
                                                   (g, e, c,
                                                     (Pulse_Syntax_Base.C_STAtomic
                                                        (new_inames, obs, sc)),
                                                     d_e, uu___)))))
                                   (fun d_e1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ ->
                                           Prims.Mkdtuple2
                                             ((with_inames c new_inames),
                                               d_e1)))))) uu___4 uu___3
              uu___2 uu___1 uu___
let (mk_bind_ghost_atomic : (unit, unit) bind_t) =
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
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (206)) (Prims.of_int (17))
                                     (Prims.of_int (206)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (205)) (Prims.of_int (72))
                                     (Prims.of_int (222)) (Prims.of_int (9)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (207))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (207))
                                                    (Prims.of_int (45)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (207))
                                                    (Prims.of_int (48))
                                                    (Prims.of_int (222))
                                                    (Prims.of_int (9)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 nvar_as_binder px
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)))
                                           (fun uu___2 ->
                                              (fun b ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (208))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (208))
                                                               (Prims.of_int (32)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (208))
                                                               (Prims.of_int (35))
                                                               (Prims.of_int (222))
                                                               (Prims.of_int (9)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            inames_of c1))
                                                      (fun uu___2 ->
                                                         (fun inames1 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (32)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (9)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    inames_of
                                                                    c2))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    inames2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun w ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    inames1
                                                                    inames2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
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
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp_ghost_l
                                                                    (g, x,
                                                                    c1, c2,
                                                                    w, (), x,
                                                                    ()))))))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.tm_join_inames
                                                                    inames1
                                                                    inames2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_inames
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (weaken_comp_inames
                                                                    g e1 c1
                                                                    d_e1
                                                                    new_inames))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c11,
                                                                    d_e11) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (weaken_comp_inames
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
                                                                    d_e2
                                                                    new_inames))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c21,
                                                                    d_e21) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c11 c21)
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c11 c21),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c11,
                                                                    c21, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c11 c21),
                                                                    d_e11,
                                                                    (),
                                                                    d_e21,
                                                                    (Pulse_Typing.Bind_comp_ghost_l
                                                                    (g, x,
                                                                    c11, c21,
                                                                    w, (), x,
                                                                    ())))))))))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           uu___2))) uu___2)))
                                 uu___)
let (mk_bind_atomic_ghost : (unit, unit) bind_t) =
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
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (227)) (Prims.of_int (17))
                                     (Prims.of_int (227)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (226)) (Prims.of_int (72))
                                     (Prims.of_int (243)) (Prims.of_int (9)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (228))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (228))
                                                    (Prims.of_int (45)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (228))
                                                    (Prims.of_int (48))
                                                    (Prims.of_int (243))
                                                    (Prims.of_int (9)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 nvar_as_binder px
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)))
                                           (fun uu___2 ->
                                              (fun b ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (229))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (229))
                                                               (Prims.of_int (32)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (229))
                                                               (Prims.of_int (35))
                                                               (Prims.of_int (243))
                                                               (Prims.of_int (9)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            inames_of c1))
                                                      (fun uu___2 ->
                                                         (fun inames1 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (32)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (9)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    inames_of
                                                                    c2))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    inames2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun w ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    inames1
                                                                    inames2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
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
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp_ghost_r
                                                                    (g, x,
                                                                    c1, c2,
                                                                    w, (), x,
                                                                    ()))))))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.tm_join_inames
                                                                    inames1
                                                                    inames2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_inames
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (weaken_comp_inames
                                                                    g e1 c1
                                                                    d_e1
                                                                    new_inames))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c11,
                                                                    d_e11) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (weaken_comp_inames
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
                                                                    d_e2
                                                                    new_inames))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c21,
                                                                    d_e21) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c11 c21)
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c11 c21),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c11,
                                                                    c21, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c11 c21),
                                                                    d_e11,
                                                                    (),
                                                                    d_e21,
                                                                    (Pulse_Typing.Bind_comp_ghost_r
                                                                    (g, x,
                                                                    c11, c21,
                                                                    w, (), x,
                                                                    ())))))))))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           uu___2))) uu___2)))
                                 uu___)
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
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (248)) (Prims.of_int (17))
                                     (Prims.of_int (248)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (247)) (Prims.of_int (72))
                                     (Prims.of_int (262)) (Prims.of_int (9)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (249))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (249))
                                                    (Prims.of_int (45)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (249))
                                                    (Prims.of_int (48))
                                                    (Prims.of_int (262))
                                                    (Prims.of_int (9)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 nvar_as_binder px
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)))
                                           (fun uu___2 ->
                                              (fun b ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (250))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (250))
                                                               (Prims.of_int (32)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (250))
                                                               (Prims.of_int (35))
                                                               (Prims.of_int (262))
                                                               (Prims.of_int (9)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            inames_of c1))
                                                      (fun uu___2 ->
                                                         (fun inames1 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (32)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (9)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    inames_of
                                                                    c2))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    inames2
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    inames1
                                                                    inames2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.tm_join_inames
                                                                    inames1
                                                                    inames2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_inames
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (weaken_comp_inames
                                                                    g e1 c1
                                                                    d_e1
                                                                    new_inames))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c11,
                                                                    d_e11) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (weaken_comp_inames
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
                                                                    d_e2
                                                                    new_inames))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c21,
                                                                    d_e21) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c11 c21)
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
                                                                    c11 c21),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c11,
                                                                    c21, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c11 c21),
                                                                    d_e11,
                                                                    (),
                                                                    d_e21,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c11, c21,
                                                                    (), x,
                                                                    ())))))))))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___2)))
                                                           uu___2))) uu___2)))
                                 uu___)
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
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (268)) (Prims.of_int (17))
                                     (Prims.of_int (268)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (267)) (Prims.of_int (72))
                                     (Prims.of_int (290)) (Prims.of_int (7)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (269))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (269))
                                                    (Prims.of_int (45)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (269))
                                                    (Prims.of_int (48))
                                                    (Prims.of_int (290))
                                                    (Prims.of_int (7)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 nvar_as_binder px
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)))
                                           (fun uu___2 ->
                                              (fun b ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (270))
                                                               (Prims.of_int (40))
                                                               (Prims.of_int (270))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Typing.Combinators.fst"
                                                               (Prims.of_int (269))
                                                               (Prims.of_int (48))
                                                               (Prims.of_int (290))
                                                               (Prims.of_int (7)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 -> c1))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            match uu___2 with
                                                            | Pulse_Syntax_Base.C_STAtomic
                                                                (inames1,
                                                                 obs1, sc1)
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    c2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
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
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.tm_join_inames
                                                                    inames1
                                                                    inames2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    new_inames
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (148)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_prop_validity
                                                                    g
                                                                    (Pulse_Typing.tm_inames_subset
                                                                    inames1
                                                                    new_inames)
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, sc1,
                                                                    inames1,
                                                                    new_inames,
                                                                    obs1,
                                                                    obs1, ())))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (new_inames,
                                                                    obs1,
                                                                    sc1)),
                                                                    d_e1,
                                                                    uu___5)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (149)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (148)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (149)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_prop_validity
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
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    obs2, ())))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    uu___5)))))
                                                                    (fun
                                                                    d_e21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
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
                                                                    uu___5)))
                                                                    uu___5))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Should have been handled separately")))
                                                                    uu___3)))
                                                           uu___2))) uu___2)))
                                 uu___)
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
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (318)) (Prims.of_int (13))
                                     (Prims.of_int (318)) (Prims.of_int (15)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (317)) (Prims.of_int (38))
                                     (Prims.of_int (368)) (Prims.of_int (82)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (319))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (319))
                                                    (Prims.of_int (41)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (320))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (368))
                                                    (Prims.of_int (82)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 nvar_as_binder px
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)))
                                           (fun uu___2 ->
                                              (fun b ->
                                                 match (c1, c2) with
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (mk_bind_st_st g
                                                             pre e1 e2 c1 c2
                                                             px d_e1 () d_e2
                                                             () ()))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (uu___2, uu___3),
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (uu___4, uu___5)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (mk_bind_ghost_ghost
                                                             g pre e1 e2 c1
                                                             c2 px d_e1 ()
                                                             d_e2 () ()))
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames1, obs1, sc1),
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (inames2, obs2, sc2)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Typing.at_most_one_observable
                                                               obs1 obs2
                                                           then
                                                             mk_bind_atomic_atomic
                                                               g pre e1 e2 c1
                                                               c2 px d_e1 ()
                                                               d_e2 () ()
                                                           else
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (46)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (81)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)))
                                                               (fun uu___3 ->
                                                                  (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1)))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    c1lifted
                                                                    c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___3)))
                                                                    uu___3)))
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___2, uu___3),
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___4) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (44)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (79)))))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)))
                                                             (fun uu___5 ->
                                                                (fun c1lifted
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    c1lifted
                                                                    c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___5)))
                                                                  uu___5)))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (uu___2, uu___3),
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (uu___4, uu___5, uu___6))
                                                     ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (mk_bind_ghost_atomic
                                                             g pre e1 e2 c1
                                                             c2 px d_e1 ()
                                                             d_e2 () ()))
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames1, uu___2, uu___3),
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (inames2, uu___4)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (mk_bind_atomic_ghost
                                                             g pre e1 e2 c1
                                                             c2 px d_e1 ()
                                                             d_e2 () ()))
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___3, uu___4))
                                                     ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___5 ->
                                                                FStar_Pervasives.Mkdtuple3
                                                                  ((Pulse_Typing.wr
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)))
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (
                                                                    Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))),
                                                                    (
                                                                    Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)), b,
                                                                    (match px
                                                                    with
                                                                    | 
                                                                    (_1, _2)
                                                                    -> _2),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))),
                                                                    d_e1, (),
                                                                    (Pulse_Typing.T_Lift
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
                                                                    c1)), c2)))),
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)), (),
                                                                    x, ()))))))))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (69)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (81)))))
                                                             (Obj.magic
                                                                (Pulse_Checker_Pure.get_non_informative_witness
                                                                   g
                                                                   (Pulse_Syntax_Base.comp_u
                                                                    c1)
                                                                   (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                             (fun uu___4 ->
                                                                (fun w ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    Pulse_Syntax_Base.Unobservable,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g, c1,
                                                                    w)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    c1lifted
                                                                    c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                  uu___4)))
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (inames, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (52)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (17)))))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                             (fun uu___4 ->
                                                                (fun g' ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g'
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c2)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    Pulse_Syntax_Base.Unobservable,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    c2lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
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
                                                                    c2lifted,
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g', c2,
                                                                    w)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2 c1
                                                                    c2lifted
                                                                    px d_e1
                                                                    () d_e21
                                                                    () ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                  uu___4)))
                                                 | (uu___2, uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             "bind either not implemented (e.g. ghost) or not possible")))
                                                uu___2))) uu___)
let (bind_res_and_post_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      Pulse_Syntax_Base.var ->
        unit Pulse_Typing.post_hint_opt ->
          ((unit * unit), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun s2 ->
               fun x ->
                 fun post_hint ->
                   match post_hint with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Combinators.fst"
                                        (Prims.of_int (380))
                                        (Prims.of_int (32))
                                        (Prims.of_int (380))
                                        (Prims.of_int (55)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Combinators.fst"
                                        (Prims.of_int (377))
                                        (Prims.of_int (13))
                                        (Prims.of_int (391))
                                        (Prims.of_int (7)))))
                               (Obj.magic
                                  (Pulse_Checker_Pure.check_universe g
                                     s2.Pulse_Syntax_Base.res))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     match uu___ with
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
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (23))
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (122)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (11))
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (122)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (384))
                                                                 (Prims.of_int (95))
                                                                 (Prims.of_int (384))
                                                                 (Prims.of_int (121)))))
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
                                                              s2.Pulse_Syntax_Base.post))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                Prims.strcat
                                                                  (Prims.strcat
                                                                    "Bound variable "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " escapes scope in postcondition "))
                                                                  (Prims.strcat
                                                                    uu___2 "")))))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        Obj.magic
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             uu___2)) uu___2))
                                           else
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (386))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (386))
                                                           (Prims.of_int (17)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (386))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (390))
                                                           (Prims.of_int (31)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 -> x))
                                                  (fun uu___3 ->
                                                     (fun y ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (61)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (31)))))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Pulse_Syntax_Naming.open_term_nv
                                                                    s2.Pulse_Syntax_Base.post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    y)))
                                                             (fun uu___3 ->
                                                                (fun
                                                                   s2_post_opened
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g y
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    s2.Pulse_Syntax_Base.res)
                                                                    s2_post_opened))
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ((), ())))))
                                                                  uu___3)))
                                                       uu___3))) uu___)))
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
                                    (fun uu___1 -> ((), ())))))) uu___3
            uu___2 uu___1 uu___
let (add_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
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
                      Pulse_Typing_Metatheory_Base.comp_typing_inversion g
                        (Pulse_Typing.add_frame c frame) c'_typing in
                    let uu___1 =
                      Pulse_Typing_Metatheory_Base.st_comp_typing_inversion g
                        (Pulse_Syntax_Base.st_comp_of_comp
                           (Pulse_Typing.add_frame c frame)) st_typing in
                    (match uu___1 with
                     | FStar_Pervasives.Mkdtuple4
                         (res_typing, pre_typing, x, post_typing) ->
                         let st_equiv =
                           Pulse_Typing.ST_VPropEquiv
                             (g, c', c'', x, (), (), (),
                               (FStar_Reflection_Typing.Rel_refl
                                  ((Pulse_Typing.elab_env g),
                                    (Pulse_Elaborate_Pure.elab_term
                                       (Pulse_Syntax_Base.comp_res c')),
                                    FStar_Reflection_Typing.R_Eq)), (), ()) in
                         let t_typing2 =
                           Pulse_Typing.T_Equiv
                             (g, t, (Pulse_Typing.add_frame c frame), c'',
                               t_typing1, st_equiv) in
                         Prims.Mkdtuple2 (c'', t_typing2))
type ('g, 'ctxt, 'postuhint) st_typing_in_ctxt =
  (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
    (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3
let rec (vprop_as_list :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term Prims.list) =
  fun vp ->
    match vp.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_Emp -> []
    | Pulse_Syntax_Base.Tm_Star (vp0, vp1) ->
        FStar_List_Tot_Base.op_At (vprop_as_list vp0) (vprop_as_list vp1)
    | uu___ -> [vp]
let rec (list_as_vprop :
  Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.term) =
  fun vps ->
    match vps with
    | [] -> Pulse_Syntax_Base.tm_emp
    | hd::[] -> hd
    | hd::tl -> Pulse_Syntax_Base.tm_star hd (list_as_vprop tl)