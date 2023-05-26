open Prims
let (check_abs :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
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
                    Pulse_Syntax_Base.ret_ty = ret_ty;
                    Pulse_Syntax_Base.post1 = post_hint1;_}
                  ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (26)) (Prims.of_int (24))
                       (Prims.of_int (26)) (Prims.of_int (38)))
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (24)) (Prims.of_int (108))
                       (Prims.of_int (56)) (Prims.of_int (28)))
                    (Obj.magic (Pulse_Checker_Pure.check_term g t1))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | FStar_Pervasives.Mkdtuple3 (t2, uu___1, uu___2)
                              ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Abs.fst"
                                      (Prims.of_int (27)) (Prims.of_int (28))
                                      (Prims.of_int (27)) (Prims.of_int (46)))
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Abs.fst"
                                      (Prims.of_int (26)) (Prims.of_int (41))
                                      (Prims.of_int (56)) (Prims.of_int (28)))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_universe g t2))
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         match uu___3 with
                                         | Prims.Mkdtuple2 (u, t_typing) ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Abs.fst"
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (19)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Abs.fst"
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (56))
                                                     (Prims.of_int (28)))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        Pulse_Typing.fresh g))
                                                  (fun uu___4 ->
                                                     (fun x ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (29))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (29))
                                                                (Prims.of_int (22)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (29))
                                                                (Prims.of_int (25))
                                                                (Prims.of_int (56))
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (56))
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (56))
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (56))
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (55))
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (14)))
                                                                    (match post_hint1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (112)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_term'
                                                                    post
                                                                    (Pulse_Syntax_Pure.tm_var
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
                                                                    Prims.int_one))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    post1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (98)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g' ret_ty
                                                                    post1))
                                                                    (fun
                                                                    post_hint_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    post_hint_typing))))
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (110)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (55))
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
                                                                    Pulse_Syntax_Base.ret_ty
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.post1
                                                                    =
                                                                    FStar_Pervasives_Native.None
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