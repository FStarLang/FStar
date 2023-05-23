open Prims
let (push_context : Prims.string -> Pulse_Typing.env -> Pulse_Typing.env) =
  fun ctx ->
    fun g ->
      {
        Pulse_Typing.f = (g.Pulse_Typing.f);
        Pulse_Typing.g = (g.Pulse_Typing.g);
        Pulse_Typing.ctxt =
          (Pulse_RuntimeUtils.extend_context ctx g.Pulse_Typing.ctxt)
      }
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (23))
         (Prims.of_int (23)) (Prims.of_int (23)) (Prims.of_int (68)))
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (23))
         (Prims.of_int (4)) (Prims.of_int (23)) (Prims.of_int (68)))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
exception Framing_failure of Pulse_Checker_Framing.framing_failure 
let (uu___is_Framing_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Framing_failure uu___ -> true | uu___ -> false
let (__proj__Framing_failure__item__uu___ :
  Prims.exn -> Pulse_Checker_Framing.framing_failure) =
  fun projectee -> match projectee with | Framing_failure uu___ -> uu___
let (try_frame_pre :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((Pulse_Syntax_Base.comp_st,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun c ->
            fun t_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (35))
                   (Prims.of_int (10)) (Prims.of_int (35))
                   (Prims.of_int (65)))
                (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (35))
                   (Prims.of_int (4)) (Prims.of_int (37)) (Prims.of_int (48)))
                (Obj.magic
                   (Pulse_Checker_Framing.try_frame_pre g t pre () c t_typing))
                (fun uu___ ->
                   match uu___ with
                   | FStar_Pervasives.Inl ok ->
                       FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ok)
                   | FStar_Pervasives.Inr fail ->
                       FStar_Tactics_Effect.raise (Framing_failure fail))
let (replace_equiv_post :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.comp ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        ((Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_equiv)
           Prims.dtuple2,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      fun post_hint ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (46))
             (Prims.of_int (48)) (Prims.of_int (46)) (Prims.of_int (65)))
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (44))
             (Prims.of_int (89)) (Prims.of_int (92)) (Prims.of_int (5)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Syntax_Base.st_comp_of_comp c))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | { Pulse_Syntax_Base.u = u_c; Pulse_Syntax_Base.res = res_c;
                    Pulse_Syntax_Base.pre = pre_c;
                    Pulse_Syntax_Base.post = post_c;_} ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (47)) (Prims.of_int (10))
                            (Prims.of_int (47)) (Prims.of_int (17)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (47)) (Prims.of_int (20))
                            (Prims.of_int (92)) (Prims.of_int (5)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Pulse_Typing.fresh g))
                         (fun uu___1 ->
                            (fun x ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (48))
                                       (Prims.of_int (11))
                                       (Prims.of_int (48))
                                       (Prims.of_int (20)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (48))
                                       (Prims.of_int (23))
                                       (Prims.of_int (92)) (Prims.of_int (5)))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          Pulse_Syntax_Base.v_as_nv x))
                                    (fun uu___1 ->
                                       (fun px ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (37)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (92))
                                                  (Prims.of_int (5)))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Pulse_Typing.extend x
                                                       (FStar_Pervasives.Inl
                                                          res_c) g))
                                               (fun uu___1 ->
                                                  (fun g_post ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.fst"
                                                             (Prims.of_int (52))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (52))
                                                             (Prims.of_int (33)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.fst"
                                                             (Prims.of_int (52))
                                                             (Prims.of_int (36))
                                                             (Prims.of_int (92))
                                                             (Prims.of_int (5)))
                                                          (Obj.magic
                                                             (Pulse_Checker_Pure.check_vprop_with_core
                                                                g pre_c))
                                                          (fun uu___1 ->
                                                             (fun
                                                                pre_c_typing
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (84)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (84)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g res_c))
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u, ty)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_univ
                                                                    u u_c
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ())
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "T_Abs: re-typechecking the return type returned different universe")))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    res_c_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (5)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post_c px))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_c_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g_post
                                                                    post_c_opened))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_c_typing
                                                                    ->
                                                                    match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g, c, c,
                                                                    x, (),
                                                                    (), (),
                                                                    (), ()))))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected variable clash with annotated postcondition")
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post px))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    g_post
                                                                    post_opened))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (72)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Framing.check_vprop_equiv
                                                                    g_post
                                                                    post_c_opened
                                                                    post_opened1
                                                                    ()))
                                                                    (fun
                                                                    post_c_post_eq
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u_c;
                                                                    Pulse_Syntax_Base.res
                                                                    = res_c;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre_c;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }),
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g, c,
                                                                    (Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u_c;
                                                                    Pulse_Syntax_Base.res
                                                                    = res_c;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre_c;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }), x,
                                                                    (), (),
                                                                    (), (),
                                                                    ())))))))
                                                                    uu___2)))
                                                                    uu___2)))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                               uu___1)))
                                                    uu___1))) uu___1)))
                              uu___1))) uu___)
let (check_abs :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            Pulse_Checker_Common.check_t ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              match t.Pulse_Syntax_Base.term1 with
              | Pulse_Syntax_Base.Tm_Abs
                  {
                    Pulse_Syntax_Base.b =
                      { Pulse_Syntax_Base.binder_ty = t1;
                        Pulse_Syntax_Base.binder_ppname = ppname;_};
                    Pulse_Syntax_Base.q = qual;
                    Pulse_Syntax_Base.pre1 = pre_hint;
                    Pulse_Syntax_Base.body = body;
                    Pulse_Syntax_Base.post1 = post_hint1;_}
                  ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (108)) (Prims.of_int (24))
                       (Prims.of_int (108)) (Prims.of_int (38)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (107)) (Prims.of_int (100))
                       (Prims.of_int (137)) (Prims.of_int (28)))
                    (Obj.magic (Pulse_Checker_Pure.check_term g t1))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | FStar_Pervasives.Mkdtuple3 (t2, uu___1, uu___2)
                              ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (109))
                                      (Prims.of_int (28))
                                      (Prims.of_int (109))
                                      (Prims.of_int (46)))
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (108))
                                      (Prims.of_int (41))
                                      (Prims.of_int (137))
                                      (Prims.of_int (28)))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_universe g t2))
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         match uu___3 with
                                         | Prims.Mkdtuple2 (u, t_typing) ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (110))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (110))
                                                     (Prims.of_int (19)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (110))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (137))
                                                     (Prims.of_int (28)))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        Pulse_Typing.fresh g))
                                                  (fun uu___4 ->
                                                     (fun x ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (111))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (111))
                                                                (Prims.of_int (22)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (111))
                                                                (Prims.of_int (25))
                                                                (Prims.of_int (137))
                                                                (Prims.of_int (28)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   (ppname,
                                                                    x)))
                                                             (fun uu___4 ->
                                                                (fun px ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    t2) g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (28)))
                                                                    (match pre_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Cannot typecheck an function without a precondition"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    pre_hint1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    pre_hint1
                                                                    px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g'
                                                                    pre_opened))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (pre_opened1,
                                                                    Pulse_Syntax_Base.Tm_VProp,
                                                                    pre_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    pre_opened1
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun pre1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match post_hint1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term'
                                                                    post
                                                                    (Pulse_Elaborate_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    FStar_Reflection_Typing.pp_name_default;
                                                                    Pulse_Syntax_Base.nm_range
                                                                    =
                                                                    FStar_Range.range_0
                                                                    })
                                                                    Prims.int_one)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (110)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14)))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)
                                                                    pre_opened1
                                                                    () post))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body',
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
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
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body' x);
                                                                    Pulse_Syntax_Base.post1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Elaborate_Pure.tm_arrow
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
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "bad hint")))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                  uu___4)))
                                                       uu___4))) uu___3)))
                         uu___)
let (has_pure_vprops : Pulse_Syntax_Base.term -> Prims.bool) =
  fun pre ->
    FStar_List_Tot_Base.existsb Pulse_Syntax_Base.uu___is_Tm_Pure
      (Pulse_Checker_Framing.vprop_as_list pre)
let (elim_pure_explicit_lid : Prims.string Prims.list) =
  Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit"
let (default_binder_annot : Pulse_Syntax_Base.binder) =
  {
    Pulse_Syntax_Base.binder_ty = Pulse_Syntax_Base.Tm_Unknown;
    Pulse_Syntax_Base.binder_ppname = FStar_Reflection_Typing.pp_name_default
  }
let (maybe_add_elim_pure :
  Pulse_Syntax_Base.term Prims.list ->
    Pulse_Syntax_Base.st_term ->
      ((Prims.bool * Pulse_Syntax_Base.st_term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun pre ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   if
                     (FStar_List_Tot_Base.length
                        (FStar_List_Tot_Base.flatten
                           (FStar_List_Tot_Base.map
                              (fun t1 ->
                                 match t1 with
                                 | Pulse_Syntax_Base.Tm_Pure p -> [p]
                                 | uu___1 -> []) pre)))
                       = Prims.int_zero
                   then (false, t)
                   else
                     (true,
                       (FStar_List_Tot_Base.fold_left
                          (fun t1 ->
                             fun p ->
                               Pulse_Typing.wr
                                 (Pulse_Syntax_Base.Tm_Bind
                                    {
                                      Pulse_Syntax_Base.binder =
                                        default_binder_annot;
                                      Pulse_Syntax_Base.head1 =
                                        (Pulse_Typing.wr
                                           (Pulse_Syntax_Base.Tm_Protect
                                              {
                                                Pulse_Syntax_Base.t =
                                                  (Pulse_Typing.wr
                                                     (Pulse_Syntax_Base.Tm_STApp
                                                        {
                                                          Pulse_Syntax_Base.head
                                                            =
                                                            (Pulse_Elaborate_Pure.tm_fvar
                                                               (Pulse_Syntax_Base.as_fv
                                                                  elim_pure_explicit_lid));
                                                          Pulse_Syntax_Base.arg_qual
                                                            =
                                                            FStar_Pervasives_Native.None;
                                                          Pulse_Syntax_Base.arg
                                                            = p
                                                        }))
                                              }));
                                      Pulse_Syntax_Base.body1 = t1
                                    })) t
                          (FStar_List_Tot_Base.flatten
                             (FStar_List_Tot_Base.map
                                (fun t1 ->
                                   match t1 with
                                   | Pulse_Syntax_Base.Tm_Pure p -> [p]
                                   | uu___2 -> []) pre))))))) uu___1 uu___
let rec (combine_if_branches :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing.env ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp_st ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  ((Pulse_Syntax_Base.comp_st,
                     (unit, unit, unit) Pulse_Typing.st_typing,
                     (unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun g_then ->
                     fun e_then ->
                       fun c_then ->
                         fun e_then_typing ->
                           fun g_else ->
                             fun e_else ->
                               fun c_else ->
                                 fun e_else_typing ->
                                   if
                                     Pulse_Syntax_Base.eq_st_comp
                                       (Pulse_Syntax_Base.st_comp_of_comp
                                          c_then)
                                       (Pulse_Syntax_Base.st_comp_of_comp
                                          c_else)
                                   then
                                     Obj.magic
                                       (Obj.repr
                                          (match (c_then, c_else) with
                                           | (Pulse_Syntax_Base.C_ST uu___,
                                              Pulse_Syntax_Base.C_ST uu___1)
                                               ->
                                               Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       FStar_Pervasives.Mkdtuple3
                                                         (c_then,
                                                           e_then_typing,
                                                           e_else_typing)))
                                           | (Pulse_Syntax_Base.C_STAtomic
                                              (inames1, uu___),
                                              Pulse_Syntax_Base.C_STAtomic
                                              (inames2, uu___1)) ->
                                               Obj.repr
                                                 (if
                                                    Pulse_Syntax_Base.eq_tm
                                                      inames1 inames2
                                                  then
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (c_then,
                                                             e_then_typing,
                                                             e_else_typing))
                                                  else
                                                    FStar_Tactics_Derived.fail
                                                      "Cannot combine then and else branches (different inames)")
                                           | (Pulse_Syntax_Base.C_STGhost
                                              (inames1, uu___),
                                              Pulse_Syntax_Base.C_STGhost
                                              (inames2, uu___1)) ->
                                               Obj.repr
                                                 (if
                                                    Pulse_Syntax_Base.eq_tm
                                                      inames1 inames2
                                                  then
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (c_then,
                                                             e_then_typing,
                                                             e_else_typing))
                                                  else
                                                    FStar_Tactics_Derived.fail
                                                      "Cannot combine then and else branches (different inames)")
                                           | (Pulse_Syntax_Base.C_ST uu___,
                                              Pulse_Syntax_Base.C_STAtomic
                                              (inames, uu___1)) ->
                                               Obj.repr
                                                 (if
                                                    Pulse_Syntax_Base.eq_tm
                                                      inames
                                                      Pulse_Syntax_Base.Tm_EmpInames
                                                  then
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (c_then,
                                                             e_then_typing,
                                                             (Pulse_Typing.T_Lift
                                                                (g_else,
                                                                  e_else,
                                                                  c_else,
                                                                  c_then,
                                                                  e_else_typing,
                                                                  (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g_else,
                                                                    c_else))))))
                                                  else
                                                    FStar_Tactics_Derived.fail
                                                      "Cannot lift STAtomic else branch to match then")
                                           | (Pulse_Syntax_Base.C_STAtomic
                                              (inames, uu___),
                                              Pulse_Syntax_Base.C_ST uu___1)
                                               ->
                                               Obj.repr
                                                 (if
                                                    Pulse_Syntax_Base.eq_tm
                                                      inames
                                                      Pulse_Syntax_Base.Tm_EmpInames
                                                  then
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (c_else,
                                                             (Pulse_Typing.T_Lift
                                                                (g_then,
                                                                  e_then,
                                                                  c_then,
                                                                  c_else,
                                                                  e_then_typing,
                                                                  (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g_then,
                                                                    c_then)))),
                                                             e_else_typing))
                                                  else
                                                    FStar_Tactics_Derived.fail
                                                      "Cannot lift STAtomic else branch to match then")
                                           | (Pulse_Syntax_Base.C_STGhost
                                              (uu___, uu___1), uu___2) ->
                                               Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (220))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (220))
                                                       (Prims.of_int (82)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (220))
                                                       (Prims.of_int (85))
                                                       (Prims.of_int (225))
                                                       (Prims.of_int (35)))
                                                    (Obj.magic
                                                       (Pulse_Checker_Pure.get_non_informative_witness
                                                          g_then
                                                          (Pulse_Syntax_Base.comp_u
                                                             c_then)
                                                          (Pulse_Syntax_Base.comp_res
                                                             c_then)))
                                                    (fun uu___3 ->
                                                       (fun w ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (222))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (222))
                                                                  (Prims.of_int (66)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (222))
                                                                  (Prims.of_int (69))
                                                                  (Prims.of_int (225))
                                                                  (Prims.of_int (35)))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g_then,
                                                                    e_then,
                                                                    c_then,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c_then),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_then))),
                                                                    e_then_typing,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g_then,
                                                                    c_then,
                                                                    w)))))
                                                               (fun uu___3 ->
                                                                  (fun
                                                                    e_then_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (combine_if_branches
                                                                    g_then
                                                                    e_then
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c_then),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_then)))
                                                                    e_then_typing1
                                                                    g_else
                                                                    e_else
                                                                    c_else
                                                                    e_else_typing))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing,
                                                                    e2_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing,
                                                                    e2_typing)))))
                                                                    uu___3)))
                                                         uu___3))
                                           | (uu___,
                                              Pulse_Syntax_Base.C_STGhost
                                              (uu___1, uu___2)) ->
                                               Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (227))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (227))
                                                       (Prims.of_int (82)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (227))
                                                       (Prims.of_int (85))
                                                       (Prims.of_int (230))
                                                       (Prims.of_int (65)))
                                                    (Obj.magic
                                                       (Pulse_Checker_Pure.get_non_informative_witness
                                                          g_else
                                                          (Pulse_Syntax_Base.comp_u
                                                             c_else)
                                                          (Pulse_Syntax_Base.comp_res
                                                             c_else)))
                                                    (fun uu___3 ->
                                                       (fun w ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (229))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (229))
                                                                  (Prims.of_int (66)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (230))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (230))
                                                                  (Prims.of_int (65)))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g_else,
                                                                    e_else,
                                                                    c_else,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c_else),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_else))),
                                                                    e_else_typing,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g_else,
                                                                    c_else,
                                                                    w)))))
                                                               (fun uu___3 ->
                                                                  (fun
                                                                    e_else_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (combine_if_branches
                                                                    g_then
                                                                    e_then
                                                                    c_then
                                                                    e_then_typing
                                                                    g_else
                                                                    e_else
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c_else),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_else)))
                                                                    e_else_typing1))
                                                                    uu___3)))
                                                         uu___3))
                                           | (uu___, uu___1) ->
                                               Obj.repr
                                                 (FStar_Tactics_Derived.fail
                                                    "Cannot combine then and else branches (incompatible effects)")))
                                   else
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Derived.fail
                                             "Cannot combine then and else branches (different st_comp)")))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (check_comp :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.comp_st ->
      unit ->
        ((unit, unit, unit) Pulse_Typing.comp_typing, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      fun pre_typing ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (246))
             (Prims.of_int (7)) (Prims.of_int (261)) (Prims.of_int (9)))
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (263))
             (Prims.of_int (4)) (Prims.of_int (278)) (Prims.of_int (44)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun st ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (246)) (Prims.of_int (27))
                       (Prims.of_int (246)) (Prims.of_int (50)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (246)) (Prims.of_int (7))
                       (Prims.of_int (261)) (Prims.of_int (9)))
                    (Obj.magic
                       (Pulse_Checker_Pure.check_universe g
                          st.Pulse_Syntax_Base.res))
                    (fun uu___1 ->
                       (fun uu___1 ->
                          match uu___1 with
                          | Prims.Mkdtuple2 (u, t_u) ->
                              if
                                Prims.op_Negation
                                  (Pulse_Syntax_Base.eq_univ u
                                     (Pulse_Syntax_Base.comp_u c))
                              then
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Derived.fail
                                        "Unexpected universe"))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (250))
                                           (Prims.of_int (18))
                                           (Prims.of_int (250))
                                           (Prims.of_int (25)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (250))
                                           (Prims.of_int (28))
                                           (Prims.of_int (260))
                                           (Prims.of_int (11)))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              Pulse_Typing.fresh g))
                                        (fun uu___3 ->
                                           (fun x ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (251))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (251))
                                                      (Prims.of_int (28)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (252))
                                                      (Prims.of_int (57))
                                                      (Prims.of_int (260))
                                                      (Prims.of_int (11)))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         Pulse_Syntax_Base.v_as_nv
                                                           x))
                                                   (fun uu___3 ->
                                                      (fun px ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (253))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (253))
                                                                 (Prims.of_int (42)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (253))
                                                                 (Prims.of_int (45))
                                                                 (Prims.of_int (260))
                                                                 (Prims.of_int (11)))
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    (st.Pulse_Syntax_Base.res))
                                                                    g))
                                                              (fun uu___3 ->
                                                                 (fun gx ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (88)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_term
                                                                    gx
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) px)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (ty,
                                                                    post_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    Pulse_Syntax_Base.Tm_VProp)
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Ill-typed postcondition"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.STC
                                                                    (g, st,
                                                                    x, (),
                                                                    (), ())))))
                                                                   uu___3)))
                                                        uu___3))) uu___3))))
                         uu___1)))
          (fun uu___ ->
             (fun check_st_comp ->
                match c with
                | Pulse_Syntax_Base.C_ST st ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (265)) (Prims.of_int (16))
                            (Prims.of_int (265)) (Prims.of_int (32)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (266)) (Prims.of_int (6))
                            (Prims.of_int (266)) (Prims.of_int (19)))
                         (Obj.magic (check_st_comp st))
                         (fun stc ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> Pulse_Typing.CT_ST (g, st, stc))))
                | Pulse_Syntax_Base.C_STAtomic (i, st) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (268)) (Prims.of_int (16))
                            (Prims.of_int (268)) (Prims.of_int (32)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (268)) (Prims.of_int (35))
                            (Prims.of_int (272)) (Prims.of_int (45)))
                         (Obj.magic (check_st_comp st))
                         (fun uu___ ->
                            (fun stc ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (269))
                                       (Prims.of_int (31))
                                       (Prims.of_int (269))
                                       (Prims.of_int (50)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (268))
                                       (Prims.of_int (35))
                                       (Prims.of_int (272))
                                       (Prims.of_int (45)))
                                    (Obj.magic
                                       (Pulse_Checker_Pure.core_check_term g
                                          i))
                                    (fun uu___ ->
                                       match uu___ with
                                       | Prims.Mkdtuple2 (ty, i_typing) ->
                                           if
                                             Prims.op_Negation
                                               (Pulse_Syntax_Base.eq_tm ty
                                                  Pulse_Syntax_Base.Tm_Inames)
                                           then
                                             FStar_Tactics_Derived.fail
                                               "Ill-typed inames"
                                           else
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Pulse_Typing.CT_STAtomic
                                                    (g, i, st, (), stc)))))
                              uu___))
                | Pulse_Syntax_Base.C_STGhost (i, st) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (274)) (Prims.of_int (16))
                            (Prims.of_int (274)) (Prims.of_int (32)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (274)) (Prims.of_int (35))
                            (Prims.of_int (278)) (Prims.of_int (44)))
                         (Obj.magic (check_st_comp st))
                         (fun uu___ ->
                            (fun stc ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (275))
                                       (Prims.of_int (31))
                                       (Prims.of_int (275))
                                       (Prims.of_int (50)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (274))
                                       (Prims.of_int (35))
                                       (Prims.of_int (278))
                                       (Prims.of_int (44)))
                                    (Obj.magic
                                       (Pulse_Checker_Pure.core_check_term g
                                          i))
                                    (fun uu___ ->
                                       match uu___ with
                                       | Prims.Mkdtuple2 (ty, i_typing) ->
                                           if
                                             Prims.op_Negation
                                               (Pulse_Syntax_Base.eq_tm ty
                                                  Pulse_Syntax_Base.Tm_Inames)
                                           then
                                             FStar_Tactics_Derived.fail
                                               "Ill-typed inames"
                                           else
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Pulse_Typing.CT_STGhost
                                                    (g, i, st, (), stc)))))
                              uu___))) uu___)
let (check_if :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.term ->
                Pulse_Checker_Common.check_t ->
                  ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                     (unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      fun e1 ->
        fun e2 ->
          fun pre ->
            fun pre_typing ->
              fun post ->
                fun check ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (291)) (Prims.of_int (6))
                       (Prims.of_int (291)) (Prims.of_int (47)))
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (290)) (Prims.of_int (3))
                       (Prims.of_int (326)) (Prims.of_int (78)))
                    (Obj.magic
                       (Pulse_Checker_Pure.check_term_with_expected_type g b
                          Pulse_Typing.tm_bool))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | Prims.Mkdtuple2 (b1, b_typing) ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (292))
                                      (Prims.of_int (14))
                                      (Prims.of_int (292))
                                      (Prims.of_int (21)))
                                   (FStar_Range.mk_range "Pulse.Checker.fst"
                                      (Prims.of_int (292))
                                      (Prims.of_int (24))
                                      (Prims.of_int (326))
                                      (Prims.of_int (78)))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> Pulse_Typing.fresh g))
                                   (fun uu___1 ->
                                      (fun hyp ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (294))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (294))
                                                 (Prims.of_int (53)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (295))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (326))
                                                 (Prims.of_int (78)))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    fun eq_v ->
                                                      Pulse_Typing.extend hyp
                                                        (FStar_Pervasives.Inl
                                                           (Pulse_Typing.mk_eq2
                                                              Pulse_Typing.u0
                                                              Pulse_Typing.tm_bool
                                                              b1 eq_v)) g))
                                              (fun uu___1 ->
                                                 (fun g_with_eq ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (300))
                                                            (Prims.of_int (7))
                                                            (Prims.of_int (314))
                                                            (Prims.of_int (35)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (318))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (326))
                                                            (Prims.of_int (78)))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               fun eq_v ->
                                                                 fun br ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    g_with_eq
                                                                    eq_v))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    g_with_eq1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g_with_eq1
                                                                    pre))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (check
                                                                    g_with_eq1
                                                                    br pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    br_typing)
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    hyp
                                                                    (Pulse_Syntax_Naming.freevars_st
                                                                    br1)
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Illegal use of control-flow hypothesis in branch"
                                                                    else
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_C_Tot
                                                                    c
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Branch computation type not st"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    br_typing)))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                         (fun uu___1 ->
                                                            (fun check_branch
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (57)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (78)))
                                                                    (
                                                                    Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_true
                                                                    e1))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e11, c1,
                                                                    e1_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_false
                                                                    e2))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (combine_if_branches
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_true)
                                                                    e11 c1
                                                                    e1_typing
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_false)
                                                                    e21 c2
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing1,
                                                                    e2_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    g c ()))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b1;
                                                                    Pulse_Syntax_Base.then_
                                                                    = e11;
                                                                    Pulse_Syntax_Base.else_
                                                                    = e21;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })), c,
                                                                    (Pulse_Typing.T_If
                                                                    (g, b1,
                                                                    e11, e21,
                                                                    c,
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c), hyp,
                                                                    (),
                                                                    e1_typing1,
                                                                    e2_typing1,
                                                                    ())))))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                              uu___1)))
                                                   uu___1))) uu___1))) uu___)
let (repack :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.comp_st,
          (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2 ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            Prims.bool ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun t ->
        fun x ->
          fun post_hint ->
            fun apply_post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (337)) (Prims.of_int (21))
                   (Prims.of_int (337)) (Prims.of_int (22)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (335)) (Prims.of_int (29))
                   (Prims.of_int (344)) (Prims.of_int (22)))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Prims.Mkdtuple2 (c, d_c) ->
                          if
                            apply_post_hint &&
                              (Pulse_Syntax_Base.stateful_comp c)
                          then
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (341))
                                       (Prims.of_int (28))
                                       (Prims.of_int (341))
                                       (Prims.of_int (60)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (340))
                                       (Prims.of_int (30))
                                       (Prims.of_int (342))
                                       (Prims.of_int (44)))
                                    (Obj.magic
                                       (replace_equiv_post g c post_hint))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            match uu___1 with
                                            | Prims.Mkdtuple2 (c1, c_c1_eq)
                                                ->
                                                FStar_Pervasives.Mkdtuple3
                                                  (t, c1,
                                                    (Pulse_Typing.T_Equiv
                                                       (g, t, c, c1, d_c,
                                                         c_c1_eq)))))))
                          else
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pervasives.Mkdtuple3 (t, c, d_c)))))
                     uu___)
let (check_elim_exists :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (355))
                 (Prims.of_int (32)) (Prims.of_int (355)) (Prims.of_int (38)))
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (354))
                 (Prims.of_int (29)) (Prims.of_int (384)) (Prims.of_int (56)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> t.Pulse_Syntax_Base.term1))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | Pulse_Syntax_Base.Tm_ElimExists
                        { Pulse_Syntax_Base.p = t1;_} ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (357)) (Prims.of_int (6))
                                (Prims.of_int (369)) (Prims.of_int (14)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (370)) (Prims.of_int (4))
                                (Prims.of_int (384)) (Prims.of_int (56)))
                             (match t1 with
                              | Pulse_Syntax_Base.Tm_Unknown ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (360))
                                             (Prims.of_int (17))
                                             (Prims.of_int (360))
                                             (Prims.of_int (34)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (360))
                                             (Prims.of_int (37))
                                             (Prims.of_int (367))
                                             (Prims.of_int (43)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                Pulse_Checker_Framing.vprop_as_list
                                                  pre))
                                          (fun uu___1 ->
                                             (fun ts ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (361))
                                                        (Prims.of_int (24))
                                                        (Prims.of_int (361))
                                                        (Prims.of_int (101)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (362))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (367))
                                                        (Prims.of_int (43)))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           FStar_List_Tot_Base.filter
                                                             (fun uu___2 ->
                                                                match uu___2
                                                                with
                                                                | Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (uu___3,
                                                                    uu___4,
                                                                    uu___5,
                                                                    uu___6)
                                                                    -> true
                                                                | uu___3 ->
                                                                    false) ts))
                                                     (fun uu___1 ->
                                                        (fun exist_tms ->
                                                           match exist_tms
                                                           with
                                                           | one::[] ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    one)))
                                                           | uu___1 ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
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
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___2))))
                                                          uu___1))) uu___1)))
                              | uu___1 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 -> t1))))
                             (fun uu___1 ->
                                (fun t2 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (371))
                                           (Prims.of_int (26))
                                           (Prims.of_int (371))
                                           (Prims.of_int (41)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (370))
                                           (Prims.of_int (4))
                                           (Prims.of_int (384))
                                           (Prims.of_int (56)))
                                        (Obj.magic
                                           (Pulse_Checker_Pure.check_vprop g
                                              t2))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Prims.Mkdtuple2
                                                  (t3, t_typing) ->
                                                  (match t3 with
                                                   | Pulse_Syntax_Base.Tm_ExistsSL
                                                       (u, ty, p, uu___2) ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (378))
                                                                  (Prims.of_int (30))
                                                                  (Prims.of_int (378))
                                                                  (Prims.of_int (49)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (373))
                                                                  (Prims.of_int (27))
                                                                  (Prims.of_int (383))
                                                                  (Prims.of_int (57)))
                                                               (Obj.magic
                                                                  (Pulse_Checker_Pure.check_universe
                                                                    g ty))
                                                               (fun uu___3 ->
                                                                  (fun uu___3
                                                                    ->
                                                                    match uu___3
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
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (24)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_ElimExists
                                                                    (g, u,
                                                                    ty, p, x,
                                                                    (), ())))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (59)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_ElimExists
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax_Base.should_elim_false))
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_elim_exists
                                                                    u ty p x)
                                                                    d))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_ElimExists
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax_Base.should_elim_false))
                                                                    }))
                                                                    uu___4
                                                                    post_hint
                                                                    true))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Universe checking failed in elim_exists")))
                                                                    uu___3)))
                                                   | uu___2 ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Derived.fail
                                                               "elim_exists argument not a Tm_ExistsSL"))))
                                             uu___1))) uu___1))) uu___)
let (is_intro_exists_erased : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = erased; Pulse_Syntax_Base.p1 = uu___;
          Pulse_Syntax_Base.witnesses = uu___1;_}
        -> erased
    | uu___ -> false
let (intro_exists_vprop :
  Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.vprop) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = uu___; Pulse_Syntax_Base.p1 = p;
          Pulse_Syntax_Base.witnesses = uu___1;_}
        -> p
let (intro_exists_witness_singleton :
  Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = uu___; Pulse_Syntax_Base.p1 = uu___1;
          Pulse_Syntax_Base.witnesses = uu___2::[];_}
        -> true
    | uu___ -> false
let (check_intro_exists_erased :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      unit FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun vprop_typing ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (412)) (Prims.of_int (46))
                   (Prims.of_int (412)) (Prims.of_int (53)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (410)) (Prims.of_int (29))
                   (Prims.of_int (430)) (Prims.of_int (56)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_IntroExists
                          { Pulse_Syntax_Base.erased = uu___1;
                            Pulse_Syntax_Base.p1 = t;
                            Pulse_Syntax_Base.witnesses = e::[];_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (414)) (Prims.of_int (4))
                                  (Prims.of_int (416)) (Prims.of_int (26)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (412)) (Prims.of_int (56))
                                  (Prims.of_int (430)) (Prims.of_int (56)))
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
                                         (match t1 with
                                          | Pulse_Syntax_Base.Tm_ExistsSL
                                              (u, ty, p, uu___3) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (421))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (421))
                                                         (Prims.of_int (49)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (419))
                                                         (Prims.of_int (27))
                                                         (Prims.of_int (429))
                                                         (Prims.of_int (58)))
                                                      (Obj.magic
                                                         (Pulse_Checker_Pure.check_universe
                                                            g ty))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match uu___4 with
                                                            | Prims.Mkdtuple2
                                                                (u',
                                                                 ty_typing)
                                                                ->
                                                                if
                                                                  Pulse_Syntax_Base.eq_univ
                                                                    u u'
                                                                then
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g e
                                                                    (Pulse_Typing.mk_erased
                                                                    u ty)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (e1,
                                                                    e_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_IntroExistsErased
                                                                    (g, u,
                                                                    ty, p,
                                                                    e1, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax_Base.should_elim_false));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e1]
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_intro_exists_erased
                                                                    u ty p e1)
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax_Base.should_elim_false));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e1]
                                                                    }))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                else
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Universe checking failed in intro_exists")))
                                                           uu___4)))
                                          | uu___3 ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Derived.fail
                                                      "elim_exists argument not a Tm_ExistsSL"))))
                                    uu___2))) uu___)
let (check_intro_exists :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      unit FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun vprop_typing ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (444)) (Prims.of_int (46))
                   (Prims.of_int (444)) (Prims.of_int (53)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (442)) (Prims.of_int (29))
                   (Prims.of_int (462)) (Prims.of_int (56)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_IntroExists
                          { Pulse_Syntax_Base.erased = uu___1;
                            Pulse_Syntax_Base.p1 = t;
                            Pulse_Syntax_Base.witnesses = e::[];_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (446)) (Prims.of_int (4))
                                  (Prims.of_int (448)) (Prims.of_int (26)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (444)) (Prims.of_int (56))
                                  (Prims.of_int (462)) (Prims.of_int (56)))
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
                                         (match t1 with
                                          | Pulse_Syntax_Base.Tm_ExistsSL
                                              (u, ty, p, uu___3) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (453))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (453))
                                                         (Prims.of_int (49)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (451))
                                                         (Prims.of_int (27))
                                                         (Prims.of_int (461))
                                                         (Prims.of_int (58)))
                                                      (Obj.magic
                                                         (Pulse_Checker_Pure.check_universe
                                                            g ty))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match uu___4 with
                                                            | Prims.Mkdtuple2
                                                                (u',
                                                                 ty_typing)
                                                                ->
                                                                if
                                                                  Pulse_Syntax_Base.eq_univ
                                                                    u u'
                                                                then
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (460))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g e ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (e1,
                                                                    e_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_IntroExists
                                                                    (g, u,
                                                                    ty, p,
                                                                    e1, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax_Base.should_elim_false));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e1]
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_intro_exists
                                                                    u ty p e1)
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p,
                                                                    Pulse_Syntax_Base.should_elim_false));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e1]
                                                                    }))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                else
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Universe checking failed in intro_exists")))
                                                           uu___4)))
                                          | uu___3 ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Derived.fail
                                                      "elim_exists argument not a Tm_ExistsSL"))))
                                    uu___2))) uu___)
let (check_intro_exists_either :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      unit FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
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
let rec (prepare_instantiations :
  (Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
    FStar_Pervasives.either) Prims.list ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        ((Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.vprop *
           (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
           FStar_Pervasives.either) Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun out ->
           fun goal_vprop ->
             fun witnesses ->
               match (witnesses, goal_vprop) with
               | ([], Pulse_Syntax_Base.Tm_ExistsSL (u, ty, p, uu___)) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (485)) (Prims.of_int (33))
                              (Prims.of_int (487)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (484)) (Prims.of_int (33))
                              (Prims.of_int (489)) (Prims.of_int (73)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (486)) (Prims.of_int (18))
                                    (Prims.of_int (486)) (Prims.of_int (29)))
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (487)) (Prims.of_int (10))
                                    (Prims.of_int (487)) (Prims.of_int (33)))
                                 (Obj.magic (Pulse_Syntax_Base.gen_uvar ()))
                                 (fun t ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         ((Pulse_Syntax_Naming.open_term' p t
                                             Prims.int_zero),
                                           (FStar_Pervasives.Inr t))))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | (next_goal_vprop, inst) ->
                                     Obj.magic
                                       (prepare_instantiations
                                          ((goal_vprop, inst) :: out)
                                          next_goal_vprop [])) uu___1)))
               | ([], uu___) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> (goal_vprop, out))))
               | (t::witnesses1, Pulse_Syntax_Base.Tm_ExistsSL
                  (u, ty, p, uu___)) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (496)) (Prims.of_int (10))
                              (Prims.of_int (501)) (Prims.of_int (35)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (494)) (Prims.of_int (45))
                              (Prims.of_int (503)) (Prims.of_int (80)))
                           (match t with
                            | Pulse_Syntax_Base.Tm_Unknown ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (498))
                                           (Prims.of_int (20))
                                           (Prims.of_int (498))
                                           (Prims.of_int (31)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (499))
                                           (Prims.of_int (12))
                                           (Prims.of_int (499))
                                           (Prims.of_int (35)))
                                        (Obj.magic
                                           (Pulse_Syntax_Base.gen_uvar ()))
                                        (fun t1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                ((Pulse_Syntax_Naming.open_term'
                                                    p t1 Prims.int_zero),
                                                  (FStar_Pervasives.Inr t1))))))
                            | uu___1 ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           ((Pulse_Syntax_Naming.open_term' p
                                               t Prims.int_zero),
                                             (FStar_Pervasives.Inl t))))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | (next_goal_vprop, inst) ->
                                     Obj.magic
                                       (prepare_instantiations
                                          ((goal_vprop, inst) :: out)
                                          next_goal_vprop witnesses1)) uu___1)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Derived.fail
                           "Unexpected number of instantiations in intro")))
          uu___2 uu___1 uu___
let (maybe_infer_intro_exists :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun pre ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (513))
             (Prims.of_int (33)) (Prims.of_int (525)) (Prims.of_int (18)))
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (526))
             (Prims.of_int (6)) (Prims.of_int (637)) (Prims.of_int (40)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun t ->
                  match FStar_List_Tot_Base.partition
                          (fun uu___1 ->
                             match uu___1 with
                             | Pulse_Syntax_Base.Tm_Pure uu___2 -> false
                             | Pulse_Syntax_Base.Tm_Emp -> false
                             | uu___2 -> true)
                          (Pulse_Checker_Framing.vprop_as_list t)
                  with
                  | (rest, pure) ->
                      (((match Pulse_Checker_Framing.list_as_vprop rest with
                         | Pulse_Syntax_Base.Tm_Star
                             (t1, Pulse_Syntax_Base.Tm_Emp) -> t1
                         | Pulse_Syntax_Base.Tm_Star
                             (Pulse_Syntax_Base.Tm_Emp, t1) -> t1
                         | t1 -> t1)), pure)))
          (fun uu___ ->
             (fun remove_pure_conjuncts ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.fst"
                        (Prims.of_int (527)) (Prims.of_int (18))
                        (Prims.of_int (544)) (Prims.of_int (17)))
                     (FStar_Range.mk_range "Pulse.Checker.fst"
                        (Prims.of_int (545)) (Prims.of_int (6))
                        (Prims.of_int (637)) (Prims.of_int (40)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun t ->
                             match t with
                             | Pulse_Syntax_Base.Tm_PureApp
                                 (Pulse_Syntax_Base.Tm_PureApp
                                  (Pulse_Syntax_Base.Tm_PureApp
                                   (hd, FStar_Pervasives_Native.Some
                                    (Pulse_Syntax_Base.Implicit), uu___1),
                                   FStar_Pervasives_Native.None, l),
                                  FStar_Pervasives_Native.None, r)
                                 ->
                                 if
                                   (match Pulse_Syntax_Util.is_fvar hd with
                                    | FStar_Pervasives_Native.Some
                                        (l1, uu___2) ->
                                        l1 =
                                          (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                             "eq2_prop")
                                    | uu___2 -> false)
                                 then FStar_Pervasives_Native.Some (l, r)
                                 else FStar_Pervasives_Native.None
                             | uu___1 -> FStar_Pervasives_Native.None))
                     (fun uu___ ->
                        (fun is_eq2 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (565)) (Prims.of_int (50))
                                   (Prims.of_int (565)) (Prims.of_int (57)))
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (545)) (Prims.of_int (6))
                                   (Prims.of_int (637)) (Prims.of_int (40)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | Pulse_Syntax_Base.Tm_IntroExists
                                          {
                                            Pulse_Syntax_Base.erased = erased;
                                            Pulse_Syntax_Base.p1 = t;
                                            Pulse_Syntax_Base.witnesses =
                                              witnesses;_}
                                          ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (566))
                                                  (Prims.of_int (28))
                                                  (Prims.of_int (566))
                                                  (Prims.of_int (43)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (565))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (637))
                                                  (Prims.of_int (40)))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.check_vprop
                                                     g t))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     match uu___1 with
                                                     | Prims.Mkdtuple2
                                                         (t1, t_typing) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (567))
                                                                 (Prims.of_int (28))
                                                                 (Prims.of_int (567))
                                                                 (Prims.of_int (65)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (566))
                                                                 (Prims.of_int (46))
                                                                 (Prims.of_int (637))
                                                                 (Prims.of_int (40)))
                                                              (Obj.magic
                                                                 (prepare_instantiations
                                                                    [] t1
                                                                    witnesses))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (goal_vprop,
                                                                    insts) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    remove_pure_conjuncts
                                                                    goal_vprop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (goal_vprop1,
                                                                    pure_conjuncts)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                    pre
                                                                    goal_vprop1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (584))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    solutions1
                                                                    ->
                                                                    fun p ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (584))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    p))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun p1
                                                                    ->
                                                                    match p1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    is_eq2 p2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (l, r) ->
                                                                    Obj.repr
                                                                    (if
                                                                    (Pulse_Checker_Inference.contains_uvar
                                                                    l) ||
                                                                    (Pulse_Checker_Inference.contains_uvar
                                                                    r)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_unify
                                                                    l r))
                                                                    (fun sols
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    sols
                                                                    solutions1)))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1))))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    maybe_solve_pure
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    maybe_solve_pure
                                                                    solutions
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun t2 ->
                                                                    match t2
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_PureApp
                                                                    (Pulse_Syntax_Base.Tm_PureApp
                                                                    (hd,
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.Implicit),
                                                                    uu___5),
                                                                    FStar_Pervasives_Native.None,
                                                                    arg) ->
                                                                    (match 
                                                                    Pulse_Syntax_Util.is_fvar
                                                                    hd
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (l, [])
                                                                    ->
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.reveal_lid
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    arg
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    un_reveal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun e ->
                                                                    Pulse_Syntax_Base.Tm_PureApp
                                                                    ((Pulse_Elaborate_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    Pulse_Reflection_Util.hide_lid)),
                                                                    FStar_Pervasives_Native.None,
                                                                    e)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    mk_hide
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (17)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (u, v) ->
                                                                    (match 
                                                                    un_reveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___6 ->
                                                                    (u,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v))
                                                                    | 
                                                                    uu___6 ->
                                                                    (u,
                                                                    (mk_hide
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)))))
                                                                    solutions1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun t2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    = t2;
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range)
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun wr
                                                                    ->
                                                                    let rec build_instantiations
                                                                    solutions3
                                                                    insts1 =
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (v, i) ->
                                                                    (match i
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    user_provided
                                                                    ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    [user_provided]
                                                                    })
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    inferred
                                                                    ->
                                                                    (match 
                                                                    un_reveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    inferred)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    sol ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [sol]
                                                                    })
                                                                    | 
                                                                    uu___6 ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    [
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    inferred]
                                                                    })))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    one_inst
                                                                    ->
                                                                    match insts1
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    | 
                                                                    hd::[] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (one_inst
                                                                    hd)
                                                                    }))))
                                                                    | 
                                                                    hd::tl ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (92)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (92)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (92)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (86)))
                                                                    (Obj.magic
                                                                    (build_instantiations
                                                                    solutions3
                                                                    tl))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (one_inst
                                                                    hd)
                                                                    }));
                                                                    Pulse_Syntax_Base.body1
                                                                    = uu___4
                                                                    }))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    wr uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = uu___4
                                                                    }))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.Tm_Protect
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    wr uu___4)))))
                                                                    uu___4) in
                                                                    Obj.magic
                                                                    (build_instantiations
                                                                    solutions2
                                                                    insts))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                   uu___2)))
                                                    uu___1))) uu___))) uu___)))
               uu___)
let (check_while :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (683)) (Prims.of_int (10))
                     (Prims.of_int (683)) (Prims.of_int (37)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (683)) (Prims.of_int (40))
                     (Prims.of_int (744)) (Prims.of_int (56)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> push_context "while loop" g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (684)) (Prims.of_int (57))
                                (Prims.of_int (684)) (Prims.of_int (63)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (683)) (Prims.of_int (40))
                                (Prims.of_int (744)) (Prims.of_int (56)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_While
                                       { Pulse_Syntax_Base.invariant = inv;
                                         Pulse_Syntax_Base.condition = cond;
                                         Pulse_Syntax_Base.body3 = body;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (686))
                                               (Prims.of_int (4))
                                               (Prims.of_int (686))
                                               (Prims.of_int (90)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (684))
                                               (Prims.of_int (66))
                                               (Prims.of_int (744))
                                               (Prims.of_int (56)))
                                            (Obj.magic
                                               (Pulse_Checker_Pure.check_vprop
                                                  (push_context "invariant"
                                                     g1)
                                                  (Pulse_Syntax_Base.Tm_ExistsSL
                                                     (Pulse_Typing.u0,
                                                       Pulse_Typing.tm_bool,
                                                       inv,
                                                       Pulse_Syntax_Base.should_elim_true))))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | Prims.Mkdtuple2
                                                      (inv1, inv_typing) ->
                                                      (match inv1 with
                                                       | Pulse_Syntax_Base.Tm_ExistsSL
                                                           (u, ty, inv2,
                                                            uu___2)
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   (Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    Pulse_Typing.tm_bool))
                                                                    ||
                                                                    (Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    u
                                                                    Pulse_Typing.u0))
                                                                 then
                                                                   Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "While loop invariant is exists but its witness type is not bool")
                                                                 else
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g1
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    cond_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    (push_context
                                                                    "while condition"
                                                                    g1) cond
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)) ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (cond1,
                                                                    cond_comp,
                                                                    cond_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_comp
                                                                    cond_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    (push_context
                                                                    "invariant for body"
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    (push_context
                                                                    "while body"
                                                                    g1) body
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)) ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    body_comp,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_comp
                                                                    body_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_While
                                                                    (g1,
                                                                    inv2,
                                                                    cond1,
                                                                    body1,
                                                                    (),
                                                                    cond_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv2;
                                                                    Pulse_Syntax_Base.condition
                                                                    = cond1;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_while
                                                                    inv2) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv2;
                                                                    Pulse_Syntax_Base.condition
                                                                    = cond1;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    }))
                                                                    uu___6
                                                                    post_hint
                                                                    true))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv2)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    body_comp))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove the inferred type of the while body matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv2)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    cond_comp))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove that the inferred type of the while condition matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___4))))
                                                       | uu___2 ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Derived.fail
                                                                   "Typechecked invariant is not an exists"))))
                                                 uu___1))) uu___))) uu___)
let (range_of_head :
  Pulse_Syntax_Base.st_term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.range)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = head; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        ->
        let rec aux t1 =
          match t1 with
          | Pulse_Syntax_Base.Tm_FStar (uu___2, r) -> (t1, r)
          | Pulse_Syntax_Base.Tm_PureApp (hd, uu___2, uu___3) -> aux hd
          | uu___2 -> (t1, FStar_Range.range_0) in
        FStar_Pervasives_Native.Some (aux head)
    | uu___ -> FStar_Pervasives_Native.None
let (tag_of_term : Pulse_Syntax_Base.term -> Prims.string) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_PureApp (hd, uu___, uu___1) -> "Tm_PureApp"
    | Pulse_Syntax_Base.Tm_Emp -> "Tm_Emp"
    | Pulse_Syntax_Base.Tm_Pure uu___ -> "Tm_Pure"
    | Pulse_Syntax_Base.Tm_Star (uu___, uu___1) -> "Tm_Star"
    | Pulse_Syntax_Base.Tm_ExistsSL (uu___, uu___1, uu___2, uu___3) ->
        "Tm_ExistsSL"
    | Pulse_Syntax_Base.Tm_ForallSL (uu___, uu___1, uu___2) -> "Tm_ForallSL"
    | Pulse_Syntax_Base.Tm_VProp -> "Tm_VProp"
    | Pulse_Syntax_Base.Tm_Inames -> "Tm_Inames"
    | Pulse_Syntax_Base.Tm_EmpInames -> "Tm_EmpInames"
    | Pulse_Syntax_Base.Tm_Unknown -> "Tm_Unknown"
    | Pulse_Syntax_Base.Tm_UVar uu___ -> "Tm_UVar"
    | Pulse_Syntax_Base.Tm_FStar (uu___, uu___1) -> "Tm_FStar"
let (maybe_log :
  Pulse_Syntax_Base.st_term -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (779))
         (Prims.of_int (4)) (Prims.of_int (785)) (Prims.of_int (16)))
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (787))
         (Prims.of_int (2)) (Prims.of_int (805)) (Prims.of_int (11)))
      (match range_of_head t with
       | FStar_Pervasives_Native.Some (head, range) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.fst"
                      (Prims.of_int (781)) (Prims.of_int (14))
                      (Prims.of_int (784)) (Prims.of_int (49)))
                   (FStar_Range.mk_range "Pulse.Checker.fst"
                      (Prims.of_int (781)) (Prims.of_int (6))
                      (Prims.of_int (784)) (Prims.of_int (49)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (784)) (Prims.of_int (25))
                            (Prims.of_int (784)) (Prims.of_int (48)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (781)) (Prims.of_int (14))
                            (Prims.of_int (784)) (Prims.of_int (49)))
                         (Obj.magic
                            (Pulse_Syntax_Printer.term_to_string head))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (781))
                                       (Prims.of_int (14))
                                       (Prims.of_int (784))
                                       (Prims.of_int (49)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (781))
                                       (Prims.of_int (14))
                                       (Prims.of_int (784))
                                       (Prims.of_int (49)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (781))
                                             (Prims.of_int (14))
                                             (Prims.of_int (784))
                                             (Prims.of_int (49)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (781))
                                             (Prims.of_int (14))
                                             (Prims.of_int (784))
                                             (Prims.of_int (49)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (782))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (782))
                                                   (Prims.of_int (50)))
                                                (FStar_Range.mk_range
                                                   "FStar.Printf.fst"
                                                   (Prims.of_int (121))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (123))
                                                   (Prims.of_int (44)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.range_to_string
                                                      range))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        fun x ->
                                                          fun x1 ->
                                                            Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    "At location "
                                                                    (
                                                                    Prims.strcat
                                                                    uu___1
                                                                    ": Checking app with head ("))
                                                                 (Prims.strcat
                                                                    x ") = "))
                                                              (Prims.strcat
                                                                 x1 "")))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  uu___1 (tag_of_term head)))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> uu___1 uu___))))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic (FStar_Tactics_Builtins.print uu___))
                        uu___)))
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))))
      (fun uu___ ->
         (fun uu___ ->
            match t.Pulse_Syntax_Base.term1 with
            | Pulse_Syntax_Base.Tm_STApp
                { Pulse_Syntax_Base.head = head;
                  Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
                  Pulse_Syntax_Base.arg = p;_}
                ->
                Obj.magic
                  (Obj.repr
                     (match Pulse_Syntax_Util.is_fvar head with
                      | FStar_Pervasives_Native.Some (l, uu___1) ->
                          Obj.repr
                            (if l = elim_pure_explicit_lid
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (792))
                                       (Prims.of_int (25))
                                       (Prims.of_int (793))
                                       (Prims.of_int (46)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (792))
                                       (Prims.of_int (17))
                                       (Prims.of_int (793))
                                       (Prims.of_int (46)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (793))
                                             (Prims.of_int (25))
                                             (Prims.of_int (793))
                                             (Prims.of_int (45)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                p))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Prims.strcat
                                                    "LOG ELIM PURE: "
                                                    (Prims.strcat uu___2 "\n")))))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Builtins.print
                                               uu___2)) uu___2))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 -> ())))
                      | uu___1 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> ()))))
            | Pulse_Syntax_Base.Tm_STApp
                {
                  Pulse_Syntax_Base.head = Pulse_Syntax_Base.Tm_PureApp
                    (head, FStar_Pervasives_Native.None, p);
                  Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
                  Pulse_Syntax_Base.arg = uu___1;_}
                ->
                Obj.magic
                  (Obj.repr
                     (match Pulse_Syntax_Util.is_fvar head with
                      | FStar_Pervasives_Native.Some (l, uu___2) ->
                          Obj.repr
                            (if
                               l =
                                 (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                    "intro_pure")
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (801))
                                       (Prims.of_int (26))
                                       (Prims.of_int (802))
                                       (Prims.of_int (47)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (801))
                                       (Prims.of_int (18))
                                       (Prims.of_int (802))
                                       (Prims.of_int (47)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (802))
                                             (Prims.of_int (26))
                                             (Prims.of_int (802))
                                             (Prims.of_int (46)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                p))
                                          (fun uu___3 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  Prims.strcat
                                                    "LOG INTRO PURE: "
                                                    (Prims.strcat uu___3 "\n")))))
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          Obj.magic
                                            (FStar_Tactics_Builtins.print
                                               uu___3)) uu___3))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 -> ())))
                      | uu___2 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> ()))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let (check_stapp :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (818)) (Prims.of_int (10))
                     (Prims.of_int (818)) (Prims.of_int (38)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (818)) (Prims.of_int (41))
                     (Prims.of_int (881)) (Prims.of_int (112)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> push_context "check_stapp" g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (820)) (Prims.of_int (14))
                                (Prims.of_int (820)) (Prims.of_int (21)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (820)) (Prims.of_int (24))
                                (Prims.of_int (881)) (Prims.of_int (112)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.range))
                             (fun uu___ ->
                                (fun range ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (821))
                                           (Prims.of_int (46))
                                           (Prims.of_int (821))
                                           (Prims.of_int (52)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (820))
                                           (Prims.of_int (24))
                                           (Prims.of_int (881))
                                           (Prims.of_int (112)))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              t.Pulse_Syntax_Base.term1))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | Pulse_Syntax_Base.Tm_STApp
                                                  {
                                                    Pulse_Syntax_Base.head =
                                                      head;
                                                    Pulse_Syntax_Base.arg_qual
                                                      = qual;
                                                    Pulse_Syntax_Base.arg =
                                                      arg;_}
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (830))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (852))
                                                          (Prims.of_int (34)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (854))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (881))
                                                          (Prims.of_int (112)))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             fun t1 ->
                                                               fun c ->
                                                                 match c with
                                                                 | Pulse_Syntax_Base.C_Tot
                                                                    ty ->
                                                                    (match 
                                                                    Pulse_Syntax_Util.is_arrow
                                                                    ty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (uu___2,
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.Implicit),
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.infer
                                                                    t1 ty pre
                                                                    range))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    false g1
                                                                    t2 pre ()
                                                                    post_hint))
                                                                    uu___4)
                                                                    | 
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unexpected c in infer_logical_implicits_and_check (head: "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", comp_typ: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", and arg: "))
                                                                    (Prims.strcat
                                                                    x1 ")")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___3))
                                                                 | uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unexpected c in infer_logical_implicits_and_check (head: "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", comp_typ: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", and arg: "))
                                                                    (Prims.strcat
                                                                    x1 ")")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___3)))
                                                       (fun uu___1 ->
                                                          (fun
                                                             infer_logical_implicits_and_check
                                                             ->
                                                             Obj.magic
                                                               (FStar_Tactics_Derived.or_else
                                                                  (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.Tm_PureApp
                                                                    (head,
                                                                    qual,
                                                                    arg)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pure_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (856))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (856))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g1
                                                                    pure_app))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (t1, ty)
                                                                    ->
                                                                    Obj.magic
                                                                    (infer_logical_implicits_and_check
                                                                    t1
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    ty)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                  (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (859))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (859))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (858))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (111)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g1 head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (head1,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    (match 
                                                                    Pulse_Syntax_Util.is_arrow
                                                                    ty_head
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ({
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = formal;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;_},
                                                                    bqual,
                                                                    comp_typ)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    qual =
                                                                    bqual
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (867))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (867))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (866))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1 arg
                                                                    formal))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (arg1,
                                                                    darg) ->
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    uu___4
                                                                    post_hint
                                                                    true))
                                                                    uu___4)))
                                                                    uu___4))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___4,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    uu___5
                                                                    post_hint
                                                                    true))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___4,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    uu___5
                                                                    post_hint
                                                                    true))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.Tm_PureApp
                                                                    (head1,
                                                                    qual,
                                                                    arg1)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    comp_typ1
                                                                    ->
                                                                    Obj.magic
                                                                    (infer_logical_implicits_and_check
                                                                    t1
                                                                    comp_typ1))
                                                                    uu___5)))
                                                                    uu___5))))
                                                                    uu___3))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected qualifier")))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (111)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (111)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (110)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Unexpected head type in impure application: "
                                                                    (Prims.strcat
                                                                    uu___4 "")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___4)))))
                                                                    uu___2))))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)
let (check_admit :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (893))
                 (Prims.of_int (43)) (Prims.of_int (893)) (Prims.of_int (49)))
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (891))
                 (Prims.of_int (29)) (Prims.of_int (916)) (Prims.of_int (4)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> t.Pulse_Syntax_Base.term1))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | Pulse_Syntax_Base.Tm_Admit
                        { Pulse_Syntax_Base.ctag1 = c;
                          Pulse_Syntax_Base.u1 = uu___1;
                          Pulse_Syntax_Base.typ = t1;
                          Pulse_Syntax_Base.post3 = post;_}
                        ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (894)) (Prims.of_int (26))
                                (Prims.of_int (894)) (Prims.of_int (44)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (893)) (Prims.of_int (52))
                                (Prims.of_int (916)) (Prims.of_int (4)))
                             (Obj.magic
                                (Pulse_Checker_Pure.check_universe g t1))
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   match uu___2 with
                                   | Prims.Mkdtuple2 (u, t_typing) ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (895))
                                               (Prims.of_int (10))
                                               (Prims.of_int (895))
                                               (Prims.of_int (17)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (895))
                                               (Prims.of_int (20))
                                               (Prims.of_int (916))
                                               (Prims.of_int (4)))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Pulse_Typing.fresh g))
                                            (fun uu___3 ->
                                               (fun x ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (896))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (896))
                                                          (Prims.of_int (20)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (896))
                                                          (Prims.of_int (23))
                                                          (Prims.of_int (916))
                                                          (Prims.of_int (4)))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             Pulse_Syntax_Base.v_as_nv
                                                               x))
                                                       (fun uu___3 ->
                                                          (fun px ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (898))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (26)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (916))
                                                                    (Prims.of_int (4)))
                                                                  (match 
                                                                    (post,
                                                                    post_hint)
                                                                   with
                                                                   | 
                                                                   (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "T_Admit: either no post or two posts"
                                                                   | 
                                                                   (FStar_Pervasives_Native.Some
                                                                    uu___3,
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___4)
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "T_Admit: either no post or two posts"
                                                                   | 
                                                                   (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    post1)
                                                                   | 
                                                                   (uu___3,
                                                                    FStar_Pervasives_Native.Some
                                                                    post1) ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    post1))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    post1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (916))
                                                                    (Prims.of_int (4)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post1 px))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (916))
                                                                    (Prims.of_int (4)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    (Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    t1) g)
                                                                    post_opened
                                                                    Pulse_Syntax_Base.Tm_VProp))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    = c;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    ({
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.typ
                                                                    =
                                                                    ({
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (Pulse_Typing.comp_admit
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }),
                                                                    (Pulse_Typing.T_Admit
                                                                    (g,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, c,
                                                                    (Pulse_Typing.STC
                                                                    (g,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, x, (),
                                                                    (), ())))))))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                            uu___3))) uu___3)))
                                  uu___2))) uu___)
let (check_return :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (928)) (Prims.of_int (10))
                   (Prims.of_int (928)) (Prims.of_int (39)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (928)) (Prims.of_int (42))
                   (Prims.of_int (947)) (Prims.of_int (52)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> push_context "check_return" g))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (929)) (Prims.of_int (53))
                              (Prims.of_int (929)) (Prims.of_int (59)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (928)) (Prims.of_int (42))
                              (Prims.of_int (947)) (Prims.of_int (52)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> t.Pulse_Syntax_Base.term1))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | Pulse_Syntax_Base.Tm_Return
                                     { Pulse_Syntax_Base.ctag = c;
                                       Pulse_Syntax_Base.insert_eq = use_eq;
                                       Pulse_Syntax_Base.term = t1;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (930))
                                             (Prims.of_int (31))
                                             (Prims.of_int (930))
                                             (Prims.of_int (54)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (929))
                                             (Prims.of_int (62))
                                             (Prims.of_int (947))
                                             (Prims.of_int (52)))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.check_term_and_type
                                                g1 t1))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple5
                                                    (t2, u, ty, uty, d) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (931))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (931))
                                                            (Prims.of_int (17)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (931))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (947))
                                                            (Prims.of_int (52)))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               Pulse_Typing.fresh
                                                                 g1))
                                                         (fun uu___2 ->
                                                            (fun x ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (20)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (52)))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (944))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (937))
                                                                    (Prims.of_int (25)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (937))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (944))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Syntax_Base.Tm_Emp
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    post))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (938))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (938))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (938))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (944))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post px))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (940))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (940))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (938))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (944))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    (Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    ty) g1)
                                                                    post_opened
                                                                    Pulse_Syntax_Base.Tm_VProp))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x), ())))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Return
                                                                    (g1, c,
                                                                    use_eq,
                                                                    u, ty,
                                                                    t2, post,
                                                                    x, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t2
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t2
                                                                    post x)
                                                                    d1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t2
                                                                    }))
                                                                    uu___3
                                                                    post_hint
                                                                    true))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)
let (handle_framing_failure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            Pulse_Checker_Framing.framing_failure ->
              Pulse_Checker_Common.check_t ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun failure ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (960)) (Prims.of_int (17))
                     (Prims.of_int (960)) (Prims.of_int (43)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (960)) (Prims.of_int (48))
                     (Prims.of_int (1027)) (Prims.of_int (30)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        fun t ->
                          {
                            Pulse_Syntax_Base.term1 = t;
                            Pulse_Syntax_Base.range =
                              (t0.Pulse_Syntax_Base.range)
                          }))
                  (fun uu___ ->
                     (fun wr ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (961)) (Prims.of_int (28))
                                (Prims.of_int (978)) (Prims.of_int (7)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (979)) (Prims.of_int (6))
                                (Prims.of_int (1027)) (Prims.of_int (30)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   fun p ->
                                     fun t ->
                                       wr
                                         (Pulse_Syntax_Base.Tm_Protect
                                            {
                                              Pulse_Syntax_Base.t =
                                                (wr
                                                   (Pulse_Syntax_Base.Tm_Bind
                                                      {
                                                        Pulse_Syntax_Base.binder
                                                          =
                                                          default_binder_annot;
                                                        Pulse_Syntax_Base.head1
                                                          =
                                                          (wr
                                                             (Pulse_Syntax_Base.Tm_Protect
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    =
                                                                    (
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_PureApp
                                                                    ((Pulse_Elaborate_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                                    "intro_pure"))),
                                                                    FStar_Pervasives_Native.None,
                                                                    p));
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.arg
                                                                    =
                                                                    Pulse_Typing.tm_unit
                                                                    }))
                                                                }));
                                                        Pulse_Syntax_Base.body1
                                                          = t
                                                      }))
                                            })))
                             (fun uu___ ->
                                (fun add_intro_pure ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (987))
                                           (Prims.of_int (6))
                                           (Prims.of_int (987))
                                           (Prims.of_int (91)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (979))
                                           (Prims.of_int (6))
                                           (Prims.of_int (1027))
                                           (Prims.of_int (30)))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              FStar_List_Tot_Base.partition
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | Pulse_Syntax_Base.Tm_Pure
                                                       uu___2 -> true
                                                   | uu___2 -> false)
                                                failure.Pulse_Checker_Framing.unmatched_preconditions))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | (pures, rest) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (990))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (996))
                                                          (Prims.of_int (13)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (997))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (1027))
                                                          (Prims.of_int (30)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Util.fold_left
                                                             (fun uu___2 ->
                                                                fun uu___1 ->
                                                                  (fun t ->
                                                                    fun p ->
                                                                    match p
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    add_intro_pure
                                                                    p1 t))
                                                                    | 
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    uu___2
                                                                    uu___1)
                                                             (wr
                                                                (Pulse_Syntax_Base.Tm_Protect
                                                                   {
                                                                    Pulse_Syntax_Base.t
                                                                    = t0
                                                                   })) pures))
                                                       (fun uu___1 ->
                                                          (fun t ->
                                                             let rec handle_intro_exists
                                                               rest1 t1 =
                                                               match rest1
                                                               with
                                                               | [] ->
                                                                   check g t1
                                                                    pre ()
                                                                    post_hint
                                                               | (Pulse_Syntax_Base.Tm_ExistsSL
                                                                   (u, ty, p,
                                                                    se))::rest2
                                                                   ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1006))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1017))
                                                                    (Prims.of_int (15)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1019))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1019))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p, se));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = []
                                                                    }))
                                                                    }));
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = t1
                                                                    }))
                                                                    }))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (handle_intro_exists
                                                                    rest2
                                                                    (wr t2)))
                                                                    uu___1)
                                                               | uu___1 ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1024))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (1024))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    failure.Pulse_Checker_Framing.remaining_context))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1021))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (1025))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1023))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (1023))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    rest1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Failed to satisfy the following preconditions:\n"
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\nContext has\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\nat command "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
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
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___2) in
                                                             Obj.magic
                                                               (handle_intro_exists
                                                                  rest t))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)
let rec (maybe_add_elims :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (1034))
             (Prims.of_int (18)) (Prims.of_int (1034)) (Prims.of_int (44)))
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (1035))
             (Prims.of_int (4)) (Prims.of_int (1065)) (Prims.of_int (30)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun t' ->
                  {
                    Pulse_Syntax_Base.term1 = t';
                    Pulse_Syntax_Base.range = (t.Pulse_Syntax_Base.range)
                  }))
          (fun uu___ ->
             (fun wr ->
                match ctxt with
                | [] ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
                | (Pulse_Syntax_Base.Tm_ExistsSL (u, ty, b, se))::rest ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (1038)) (Prims.of_int (14))
                               (Prims.of_int (1038)) (Prims.of_int (86)))
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (1038)) (Prims.of_int (89))
                               (Prims.of_int (1048)) (Prims.of_int (35)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  wr
                                    (Pulse_Syntax_Base.Tm_Protect
                                       {
                                         Pulse_Syntax_Base.t =
                                           (wr
                                              (Pulse_Syntax_Base.Tm_ElimExists
                                                 {
                                                   Pulse_Syntax_Base.p =
                                                     (Pulse_Syntax_Base.Tm_ExistsSL
                                                        (u, ty, b, se))
                                                 }))
                                       })))
                            (fun uu___ ->
                               (fun e ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (1039))
                                          (Prims.of_int (14))
                                          (Prims.of_int (1039))
                                          (Prims.of_int (21)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (1039))
                                          (Prims.of_int (24))
                                          (Prims.of_int (1048))
                                          (Prims.of_int (35)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ -> Pulse_Typing.fresh g))
                                       (fun uu___ ->
                                          (fun x ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (1040))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (1040))
                                                     (Prims.of_int (24)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (1040))
                                                     (Prims.of_int (27))
                                                     (Prims.of_int (1048))
                                                     (Prims.of_int (35)))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
                                                        Pulse_Syntax_Base.v_as_nv
                                                          x))
                                                  (fun uu___ ->
                                                     (fun px ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1041))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (1041))
                                                                (Prims.of_int (33)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1041))
                                                                (Prims.of_int (36))
                                                                (Prims.of_int (1048))
                                                                (Prims.of_int (35)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___ ->
                                                                   Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    ty) g))
                                                             (fun uu___ ->
                                                                (fun g1 ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1042))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1042))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1042))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (1048))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    b px))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun b1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (1048))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (maybe_add_elims
                                                                    g1 [b1] t))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1044))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1044))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1044))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (1048))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    t1 x))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1045))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1047))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1048))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1048))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e;
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = t2
                                                                    }))
                                                                    }))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t3
                                                                    ->
                                                                    Obj.magic
                                                                    (maybe_add_elims
                                                                    g1 rest
                                                                    (wr t3)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                  uu___)))
                                                       uu___))) uu___)))
                                 uu___)))
                | (Pulse_Syntax_Base.Tm_Pure p)::rest ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (1051)) (Prims.of_int (8))
                               (Prims.of_int (1053)) (Prims.of_int (33)))
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (1055)) (Prims.of_int (6))
                               (Prims.of_int (1059)) (Prims.of_int (7)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  wr
                                    (Pulse_Syntax_Base.Tm_STApp
                                       {
                                         Pulse_Syntax_Base.head =
                                           (Pulse_Elaborate_Pure.tm_fvar
                                              (Pulse_Syntax_Base.as_fv
                                                 elim_pure_explicit_lid));
                                         Pulse_Syntax_Base.arg_qual =
                                           FStar_Pervasives_Native.None;
                                         Pulse_Syntax_Base.arg = p
                                       })))
                            (fun uu___ ->
                               (fun elim_pure_tm ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (1055))
                                          (Prims.of_int (9))
                                          (Prims.of_int (1059))
                                          (Prims.of_int (7)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (1055))
                                          (Prims.of_int (6))
                                          (Prims.of_int (1059))
                                          (Prims.of_int (7)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.fst"
                                                (Prims.of_int (1056))
                                                (Prims.of_int (18))
                                                (Prims.of_int (1058))
                                                (Prims.of_int (73)))
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.fst"
                                                (Prims.of_int (1055))
                                                (Prims.of_int (9))
                                                (Prims.of_int (1059))
                                                (Prims.of_int (7)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (1058))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (1058))
                                                      (Prims.of_int (73)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (1056))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (1058))
                                                      (Prims.of_int (73)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (1058))
                                                            (Prims.of_int (28))
                                                            (Prims.of_int (1058))
                                                            (Prims.of_int (73)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (1058))
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (1058))
                                                            (Prims.of_int (73)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1058))
                                                                  (Prims.of_int (42))
                                                                  (Prims.of_int (1058))
                                                                  (Prims.of_int (70)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (1058))
                                                                  (Prims.of_int (28))
                                                                  (Prims.of_int (1058))
                                                                  (Prims.of_int (73)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1058))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (1058))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1058))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (1058))
                                                                    (Prims.of_int (70)))
                                                                    (Obj.magic
                                                                    (maybe_add_elims
                                                                    g rest t))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = uu___
                                                                    }))))
                                                               (fun uu___ ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.Tm_Protect
                                                                    uu___))))
                                                         (fun uu___ ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 wr uu___))))
                                                   (fun uu___ ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           {
                                                             Pulse_Syntax_Base.binder
                                                               =
                                                               default_binder_annot;
                                                             Pulse_Syntax_Base.head1
                                                               =
                                                               (wr
                                                                  (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    elim_pure_tm
                                                                    }));
                                                             Pulse_Syntax_Base.body1
                                                               = uu___
                                                           }))))
                                             (fun uu___ ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Pulse_Syntax_Base.Tm_Bind
                                                       uu___))))
                                       (fun uu___ ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 -> wr uu___)))) uu___)))
                | (Pulse_Syntax_Base.Tm_Star (p, q))::rest ->
                    Obj.magic
                      (Obj.repr (maybe_add_elims g (p :: q :: rest) t))
                | uu___::rest ->
                    Obj.magic (Obj.repr (maybe_add_elims g rest t))) uu___)
let rec (unprotect : Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    let wr t0 =
      {
        Pulse_Syntax_Base.term1 = t0;
        Pulse_Syntax_Base.range = (t.Pulse_Syntax_Base.range)
      } in
    let protect t1 =
      {
        Pulse_Syntax_Base.term1 =
          (Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1 });
        Pulse_Syntax_Base.range = (t1.Pulse_Syntax_Base.range)
      } in
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Protect
        {
          Pulse_Syntax_Base.t =
            {
              Pulse_Syntax_Base.term1 = Pulse_Syntax_Base.Tm_Bind
                { Pulse_Syntax_Base.binder = binder;
                  Pulse_Syntax_Base.head1 = head;
                  Pulse_Syntax_Base.body1 = body;_};
              Pulse_Syntax_Base.range = uu___;_};_}
        ->
        wr
          (Pulse_Syntax_Base.Tm_Bind
             {
               Pulse_Syntax_Base.binder = binder;
               Pulse_Syntax_Base.head1 = (protect head);
               Pulse_Syntax_Base.body1 = body
             })
    | Pulse_Syntax_Base.Tm_Protect
        {
          Pulse_Syntax_Base.t =
            {
              Pulse_Syntax_Base.term1 = Pulse_Syntax_Base.Tm_If
                { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
                  Pulse_Syntax_Base.else_ = else_;
                  Pulse_Syntax_Base.post2 = post;_};
              Pulse_Syntax_Base.range = uu___;_};_}
        ->
        wr
          (Pulse_Syntax_Base.Tm_If
             {
               Pulse_Syntax_Base.b1 = b;
               Pulse_Syntax_Base.then_ = (protect then_);
               Pulse_Syntax_Base.else_ = (protect else_);
               Pulse_Syntax_Base.post2 = post
             })
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
        unprotect t1
    | uu___ -> t
let (auto_elims :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun ctxt ->
             fun t ->
               match t.Pulse_Syntax_Base.term1 with
               | Pulse_Syntax_Base.Tm_Protect uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> unprotect t)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (1083)) (Prims.of_int (15))
                              (Prims.of_int (1083)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (1083)) (Prims.of_int (36))
                              (Prims.of_int (1085)) (Prims.of_int (15)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Checker_Framing.vprop_as_list ctxt))
                           (fun uu___1 ->
                              (fun ctxt1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (1084))
                                         (Prims.of_int (12))
                                         (Prims.of_int (1084))
                                         (Prims.of_int (36)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (1085))
                                         (Prims.of_int (4))
                                         (Prims.of_int (1085))
                                         (Prims.of_int (15)))
                                      (Obj.magic (maybe_add_elims g ctxt1 t))
                                      (fun t1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> unprotect t1))))
                                uu___1)))) uu___2 uu___1 uu___
let rec (print_st_head : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Abs"
    | Pulse_Syntax_Base.Tm_Protect p -> print_st_head p.Pulse_Syntax_Base.t
    | Pulse_Syntax_Base.Tm_Return p -> print_head p.Pulse_Syntax_Base.term
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
and (print_head : Pulse_Syntax_Base.term -> Prims.string) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_PureApp (head, uu___, uu___1) -> print_head head
    | uu___ -> "<pure term>"
let rec (print_skel : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = uu___; Pulse_Syntax_Base.q = uu___1;
          Pulse_Syntax_Base.pre1 = uu___2; Pulse_Syntax_Base.body = body;
          Pulse_Syntax_Base.post1 = uu___3;_}
        -> Prims.strcat "(fun _ -> " (Prims.strcat (print_skel body) ")")
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = p;_} ->
        Prims.strcat "(Protect " (Prims.strcat (print_skel p) ")")
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.ctag = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1; Pulse_Syntax_Base.term = p;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = uu___; Pulse_Syntax_Base.head1 = e1;
          Pulse_Syntax_Base.body1 = e2;_}
        ->
        Prims.strcat
          (Prims.strcat "(Bind " (Prims.strcat (print_skel e1) " "))
          (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.head2 = uu___; Pulse_Syntax_Base.body2 = e2;_} ->
        Prims.strcat "(TotBind _ " (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
let (check_par :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (1142)) (Prims.of_int (10))
                     (Prims.of_int (1142)) (Prims.of_int (36)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (1142)) (Prims.of_int (39))
                     (Prims.of_int (1168)) (Prims.of_int (34)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> push_context "check_par" g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (1144)) (Prims.of_int (50))
                                (Prims.of_int (1144)) (Prims.of_int (56)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (1142)) (Prims.of_int (39))
                                (Prims.of_int (1168)) (Prims.of_int (34)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_Par
                                       { Pulse_Syntax_Base.pre11 = preL;
                                         Pulse_Syntax_Base.body11 = eL;
                                         Pulse_Syntax_Base.post11 = postL;
                                         Pulse_Syntax_Base.pre2 = preR;
                                         Pulse_Syntax_Base.body21 = eR;
                                         Pulse_Syntax_Base.post21 = postR;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (1146))
                                               (Prims.of_int (4))
                                               (Prims.of_int (1146))
                                               (Prims.of_int (49)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (1144))
                                               (Prims.of_int (59))
                                               (Prims.of_int (1168))
                                               (Prims.of_int (34)))
                                            (Obj.magic
                                               (Pulse_Checker_Pure.check_term_with_expected_type
                                                  g1 preL
                                                  Pulse_Syntax_Base.Tm_VProp))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | Prims.Mkdtuple2
                                                      (preL1, preL_typing) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.fst"
                                                              (Prims.of_int (1148))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (1148))
                                                              (Prims.of_int (49)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.fst"
                                                              (Prims.of_int (1146))
                                                              (Prims.of_int (52))
                                                              (Prims.of_int (1168))
                                                              (Prims.of_int (34)))
                                                           (Obj.magic
                                                              (Pulse_Checker_Pure.check_term_with_expected_type
                                                                 g1 preR
                                                                 Pulse_Syntax_Base.Tm_VProp))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 match uu___2
                                                                 with
                                                                 | Prims.Mkdtuple2
                                                                    (preR1,
                                                                    preR_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1151))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1151))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1148))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (1168))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eL
                                                                    preL1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postL)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eL1, cL,
                                                                    eL_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_C_ST
                                                                    cL
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1157))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (1157))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1157))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (1167))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    g1 cL ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1159))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1159))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1157))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (1167))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eR
                                                                    preR1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postR)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eR1, cR,
                                                                    eR_typing)
                                                                    ->
                                                                    if
                                                                    (Pulse_Syntax_Base.uu___is_C_ST
                                                                    cR) &&
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    cL)
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    cR))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1163))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1163))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1163))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    g1 cR ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1164))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1164))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1164))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1165))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1165))
                                                                    (Prims.of_int (71)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Par
                                                                    (g1, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1166))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre11
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post21
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_par
                                                                    cL cR x)
                                                                    d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre11
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post21
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    }))
                                                                    uu___5
                                                                    post_hint
                                                                    true))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "par: cR is not stt")))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "par: cL is not stt")))
                                                                    uu___3)))
                                                                uu___2)))
                                                 uu___1))) uu___))) uu___)
let (check_withlocal :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (1182)) (Prims.of_int (10))
                     (Prims.of_int (1182)) (Prims.of_int (42)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (1182)) (Prims.of_int (45))
                     (Prims.of_int (1224)) (Prims.of_int (57)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> push_context "check_withlocal" g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (1183)) (Prims.of_int (16))
                                (Prims.of_int (1183)) (Prims.of_int (42)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (1183)) (Prims.of_int (47))
                                (Prims.of_int (1224)) (Prims.of_int (57)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   fun t0 ->
                                     {
                                       Pulse_Syntax_Base.term1 = t0;
                                       Pulse_Syntax_Base.range =
                                         (t.Pulse_Syntax_Base.range)
                                     }))
                             (fun uu___ ->
                                (fun wr ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (1184))
                                           (Prims.of_int (46))
                                           (Prims.of_int (1184))
                                           (Prims.of_int (52)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (1183))
                                           (Prims.of_int (47))
                                           (Prims.of_int (1224))
                                           (Prims.of_int (57)))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              t.Pulse_Syntax_Base.term1))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | Pulse_Syntax_Base.Tm_WithLocal
                                                  {
                                                    Pulse_Syntax_Base.initializer1
                                                      = init;
                                                    Pulse_Syntax_Base.body4 =
                                                      body;_}
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (1186))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (1186))
                                                          (Prims.of_int (30)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (1184))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (1224))
                                                          (Prims.of_int (57)))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.check_term_and_type
                                                             g1 init))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Mkdtuple5
                                                                 (init1,
                                                                  init_u,
                                                                  init_t,
                                                                  init_t_typing,
                                                                  init_typing)
                                                                 ->
                                                                 if
                                                                   Pulse_Syntax_Base.eq_univ
                                                                    init_u
                                                                    Pulse_Typing.u0
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1188))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1188))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1188))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1189))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (1189))
                                                                    (Prims.of_int (25)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1190))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun px
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars_st
                                                                    body)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "withlocal: x is free in body"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1193))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (1193))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1193))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Elaborate_Pure.null_var
                                                                    x))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1194))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (1194))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1194))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Typing.mk_ref
                                                                    init_t))
                                                                    g1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    g_extended
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1195))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1195))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1195))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.comp_withlocal_body_pre
                                                                    pre
                                                                    init_t
                                                                    x_tm
                                                                    init1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1196))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (1196))
                                                                    (Prims.of_int (72)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1196))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g_extended
                                                                    body_pre))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1199))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (1205))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1205))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1201))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1203))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1203))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (1205))
                                                                    (Prims.of_int (36)))
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    post)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "withlocal: no post_hint!")
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1204))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (1204))
                                                                    (Prims.of_int (83)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1203))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (1205))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    g_extended
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post px)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened,
                                                                    uu___5)
                                                                    ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1206))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1206))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1206))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.comp_withlocal_body_post
                                                                    post
                                                                    init_t
                                                                    x_tm))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1208))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1208))
                                                                    (Prims.of_int (107)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1206))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g_extended
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)
                                                                    body_pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_post)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (opened_body,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    ((Pulse_Syntax_Base.uu___is_C_ST
                                                                    c_body)
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c_body)
                                                                    body_post))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "withlocal: body is not stt or postcondition mismatch"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1214))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1214))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1215))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    opened_body
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1216))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1216))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1216))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.C_ST
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c_body);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c_body);
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    = post
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1218))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (1218))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1221))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1223))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (check_comp
                                                                    g1 c ()))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.initializer1
                                                                    = init1;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body1
                                                                    })), c,
                                                                    (Pulse_Typing.T_WithLocal
                                                                    (g1,
                                                                    init1,
                                                                    body1,
                                                                    init_t,
                                                                    c, x, (),
                                                                    (),
                                                                    c_typing,
                                                                    body_typing)))))))
                                                                    uu___5)))
                                                                    uu___5))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "withlocal: init type is not universe zero")))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)
let (check_rewrite :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (1236))
                 (Prims.of_int (10)) (Prims.of_int (1236))
                 (Prims.of_int (40)))
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (1236))
                 (Prims.of_int (43)) (Prims.of_int (1249))
                 (Prims.of_int (52)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> push_context "check_rewrite" g))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (1237)) (Prims.of_int (32))
                            (Prims.of_int (1237)) (Prims.of_int (38)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (1236)) (Prims.of_int (43))
                            (Prims.of_int (1249)) (Prims.of_int (52)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> t.Pulse_Syntax_Base.term1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Pulse_Syntax_Base.Tm_Rewrite
                                   { Pulse_Syntax_Base.t1 = p;
                                     Pulse_Syntax_Base.t2 = q;_}
                                   ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (1238))
                                           (Prims.of_int (26))
                                           (Prims.of_int (1238))
                                           (Prims.of_int (41)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (1237))
                                           (Prims.of_int (41))
                                           (Prims.of_int (1249))
                                           (Prims.of_int (52)))
                                        (Obj.magic
                                           (Pulse_Checker_Pure.check_vprop g1
                                              p))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Prims.Mkdtuple2
                                                  (p1, p_typing) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (1239))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (1239))
                                                          (Prims.of_int (41)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (1238))
                                                          (Prims.of_int (44))
                                                          (Prims.of_int (1249))
                                                          (Prims.of_int (52)))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.check_vprop
                                                             g1 q))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             match uu___2
                                                             with
                                                             | Prims.Mkdtuple2
                                                                 (q1,
                                                                  q_typing)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1241))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1247))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1247))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (52)))
                                                                    (if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    p1 q1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ())))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1243))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1243))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1243))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1247))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g1)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    p1)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    q1)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    issues)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1245))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1246))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1245))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1246))
                                                                    (Prims.of_int (67)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1246))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (1246))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.print_issues
                                                                    issues))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "rewrite: p and q elabs are not equiv\n"
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___5)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    equiv_p_q
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1248))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1248))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Rewrite
                                                                    (g1, p1,
                                                                    q1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1249))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = p1;
                                                                    Pulse_Syntax_Base.t2
                                                                    = q1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_rewrite
                                                                    p1 q1) d))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (repack g
                                                                    pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = p1;
                                                                    Pulse_Syntax_Base.t2
                                                                    = q1
                                                                    }))
                                                                    uu___3
                                                                    post_hint
                                                                    true))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                            uu___2))) uu___1)))
                              uu___))) uu___)
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (1261)) (Prims.of_int (4))
                   (Prims.of_int (1263)) (Prims.of_int (10)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (1265)) (Prims.of_int (2))
                   (Prims.of_int (1338)) (Prims.of_int (18)))
                (if allow_inst
                 then Obj.magic (Obj.repr (auto_elims g pre t))
                 else
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t))))
                (fun uu___ ->
                   (fun t1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (1265)) (Prims.of_int (2))
                              (Prims.of_int (1267)) (Prims.of_int (68)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (1268)) (Prims.of_int (2))
                              (Prims.of_int (1338)) (Prims.of_int (18)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (1265)) (Prims.of_int (10))
                                    (Prims.of_int (1267)) (Prims.of_int (68)))
                                 (FStar_Range.mk_range "Pulse.Checker.fst"
                                    (Prims.of_int (1265)) (Prims.of_int (2))
                                    (Prims.of_int (1267)) (Prims.of_int (68)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (1267))
                                          (Prims.of_int (26))
                                          (Prims.of_int (1267))
                                          (Prims.of_int (67)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (1265))
                                          (Prims.of_int (10))
                                          (Prims.of_int (1267))
                                          (Prims.of_int (68)))
                                       (Obj.magic
                                          (Pulse_Syntax_Printer.term_to_string
                                             pre))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (1265))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (1267))
                                                     (Prims.of_int (68)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (1265))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (1267))
                                                     (Prims.of_int (68)))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (1266))
                                                           (Prims.of_int (26))
                                                           (Prims.of_int (1266))
                                                           (Prims.of_int (53)))
                                                        (FStar_Range.mk_range
                                                           "FStar.Printf.fst"
                                                           (Prims.of_int (121))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (123))
                                                           (Prims.of_int (44)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Builtins.range_to_string
                                                              t1.Pulse_Syntax_Base.range))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                fun x ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    "At "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": precondition is "))
                                                                    (
                                                                    Prims.strcat
                                                                    x "\n")))))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          uu___1 uu___))))
                                            uu___)))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       Obj.magic
                                         (FStar_Tactics_Builtins.print uu___))
                                      uu___)))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Derived.try_with
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match () with
                                            | () ->
                                                (match t1.Pulse_Syntax_Base.term1
                                                 with
                                                 | Pulse_Syntax_Base.Tm_Protect
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Derived.fail
                                                             "Protect should have been removed"))
                                                 | Pulse_Syntax_Base.Tm_Return
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_return
                                                             allow_inst g t1
                                                             pre () post_hint))
                                                 | Pulse_Syntax_Base.Tm_Abs
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_abs g t1 pre
                                                             () post_hint
                                                             (check' true)))
                                                 | Pulse_Syntax_Base.Tm_STApp
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_stapp
                                                             allow_inst g t1
                                                             pre () post_hint
                                                             check'))
                                                 | Pulse_Syntax_Base.Tm_Bind
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (Pulse_Checker_Bind.check_bind
                                                             g t1 pre ()
                                                             post_hint
                                                             (check' true)))
                                                 | Pulse_Syntax_Base.Tm_TotBind
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (Pulse_Checker_Bind.check_tot_bind
                                                             g t1 pre ()
                                                             post_hint
                                                             (check' true)))
                                                 | Pulse_Syntax_Base.Tm_If
                                                     {
                                                       Pulse_Syntax_Base.b1 =
                                                         b;
                                                       Pulse_Syntax_Base.then_
                                                         = e1;
                                                       Pulse_Syntax_Base.else_
                                                         = e2;
                                                       Pulse_Syntax_Base.post2
                                                         = post_if;_}
                                                     ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1290))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (1293))
                                                                (Prims.of_int (69)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1295))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (1295))
                                                                (Prims.of_int (58)))
                                                             (match (post_if,
                                                                    post_hint)
                                                              with
                                                              | (FStar_Pervasives_Native.None,
                                                                 FStar_Pervasives_Native.Some
                                                                 p) ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    p)
                                                              | (FStar_Pervasives_Native.Some
                                                                 p,
                                                                 FStar_Pervasives_Native.None)
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    p)
                                                              | (uu___2,
                                                                 uu___3) ->
                                                                  FStar_Tactics_Derived.fail
                                                                    "Either two annotations for if post or none")
                                                             (fun uu___2 ->
                                                                (fun post ->
                                                                   Obj.magic
                                                                    (check_if
                                                                    g b e1 e2
                                                                    pre ()
                                                                    post
                                                                    (check'
                                                                    true)))
                                                                  uu___2)))
                                                 | Pulse_Syntax_Base.Tm_ElimExists
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_elim_exists
                                                             g t1 pre ()
                                                             post_hint))
                                                 | Pulse_Syntax_Base.Tm_IntroExists
                                                     {
                                                       Pulse_Syntax_Base.erased
                                                         = uu___2;
                                                       Pulse_Syntax_Base.p1 =
                                                         uu___3;
                                                       Pulse_Syntax_Base.witnesses
                                                         = witnesses;_}
                                                     ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1302))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (1308))
                                                                (Prims.of_int (19)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (1310))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (1319))
                                                                (Prims.of_int (7)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   match witnesses
                                                                   with
                                                                   | 
                                                                   w::[] ->
                                                                    (match w
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    -> true
                                                                    | 
                                                                    uu___5 ->
                                                                    false)
                                                                   | 
                                                                   uu___5 ->
                                                                    true))
                                                             (fun uu___4 ->
                                                                (fun
                                                                   should_infer_witnesses
                                                                   ->
                                                                   if
                                                                    should_infer_witnesses
                                                                   then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1312))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (1312))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (1315))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1315))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (maybe_infer_intro_exists
                                                                    g t1 pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    unary_intros
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g
                                                                    unary_intros
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___4))
                                                                   else
                                                                    Obj.magic
                                                                    (check_intro_exists_either
                                                                    g t1
                                                                    FStar_Pervasives_Native.None
                                                                    pre ()
                                                                    post_hint))
                                                                  uu___4)))
                                                 | Pulse_Syntax_Base.Tm_While
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_while
                                                             allow_inst g t1
                                                             pre () post_hint
                                                             check'))
                                                 | Pulse_Syntax_Base.Tm_Admit
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_admit g t1
                                                             pre () post_hint))
                                                 | Pulse_Syntax_Base.Tm_Par
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_par
                                                             allow_inst g t1
                                                             pre () post_hint
                                                             check'))
                                                 | Pulse_Syntax_Base.Tm_WithLocal
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_withlocal
                                                             allow_inst g t1
                                                             pre () post_hint
                                                             check'))
                                                 | Pulse_Syntax_Base.Tm_Rewrite
                                                     uu___2 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (check_rewrite g t1
                                                             pre () post_hint))))
                                           uu___1)
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | Framing_failure failure ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (handle_framing_failure
                                                        g t1 pre () post_hint
                                                        failure (check' true)))
                                            | e ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.raise
                                                        e))) uu___1))) uu___)))
                     uu___)
let (check : Pulse_Checker_Common.check_t) = check' true