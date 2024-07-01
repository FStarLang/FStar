open Prims
let (debug_abs :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.abs"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                              (Prims.of_int (40)) (Prims.of_int (15))
                              (Prims.of_int (40)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                              (Prims.of_int (40)) (Prims.of_int (7))
                              (Prims.of_int (40)) (Prims.of_int (21)))))
                     (Obj.magic (s ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (range_of_st_comp : Pulse_Syntax_Base.st_comp -> FStar_Range.range) =
  fun st ->
    Pulse_RuntimeUtils.union_ranges
      (Pulse_RuntimeUtils.range_of_term st.Pulse_Syntax_Base.pre)
      (Pulse_RuntimeUtils.range_of_term st.Pulse_Syntax_Base.post)
let (range_of_comp : Pulse_Syntax_Base.comp -> FStar_Range.range) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t -> Pulse_RuntimeUtils.range_of_term t
    | Pulse_Syntax_Base.C_ST st -> range_of_st_comp st
    | Pulse_Syntax_Base.C_STAtomic (uu___, uu___1, st) -> range_of_st_comp st
    | Pulse_Syntax_Base.C_STGhost (uu___, st) -> range_of_st_comp st
let rec (arrow_of_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Syntax_Base.term * Pulse_Syntax_Base.st_term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun env ->
    fun prog ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (56)) (Prims.of_int (44)) (Prims.of_int (56))
                 (Prims.of_int (53)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (56)) (Prims.of_int (3)) (Prims.of_int (114))
                 (Prims.of_int (5)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> prog.Pulse_Syntax_Base.term1))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | Pulse_Syntax_Base.Tm_Abs
                  { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                    Pulse_Syntax_Base.ascription = ascription;
                    Pulse_Syntax_Base.body = body;_}
                  ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (57)) (Prims.of_int (12))
                                (Prims.of_int (57)) (Prims.of_int (21)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (57)) (Prims.of_int (24))
                                (Prims.of_int (114)) (Prims.of_int (5)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Typing_Env.fresh env))
                       (fun uu___1 ->
                          (fun x ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (58))
                                           (Prims.of_int (13))
                                           (Prims.of_int (58))
                                           (Prims.of_int (31)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (58))
                                           (Prims.of_int (34))
                                           (Prims.of_int (114))
                                           (Prims.of_int (5)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        ((b.Pulse_Syntax_Base.binder_ppname),
                                          x)))
                                  (fun uu___1 ->
                                     (fun px ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (59))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (59))
                                                      (Prims.of_int (53)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (59))
                                                      (Prims.of_int (56))
                                                      (Prims.of_int (114))
                                                      (Prims.of_int (5)))))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Typing_Env.push_binding
                                                     env x
                                                     (FStar_Pervasives_Native.fst
                                                        px)
                                                     b.Pulse_Syntax_Base.binder_ty))
                                             (fun uu___1 ->
                                                (fun env1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Abs.fst"
                                                                 (Prims.of_int (60))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (60))
                                                                 (Prims.of_int (38)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Abs.fst"
                                                                 (Prims.of_int (60))
                                                                 (Prims.of_int (41))
                                                                 (Prims.of_int (114))
                                                                 (Prims.of_int (5)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___1 ->
                                                              Pulse_Syntax_Naming.open_st_term_nv
                                                                body px))
                                                        (fun uu___1 ->
                                                           (fun body1 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (36)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (5)))))
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ascription.Pulse_Syntax_Base.annotated))
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    annot ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (5)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    ascription.Pulse_Syntax_Base.elaborated
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (prog.Pulse_Syntax_Base.range1))
                                                                    "Unexpected elaborated annotation on function"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Abs
                                                                    body1.Pulse_Syntax_Base.term1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match annot
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    (arrow_of_abs
                                                                    env1
                                                                    body1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (arr,
                                                                    body2) ->
                                                                    ((Pulse_Syntax_Pure.wr
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    b q
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    arr x)))
                                                                    (Pulse_RuntimeUtils.union_ranges
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    b.Pulse_Syntax_Base.binder_ty)
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    arr x)))),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body2 x)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.effect_tag)
                                                                    })))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Naming.open_comp_with
                                                                    c
                                                                    (Pulse_Syntax_Pure.term_of_nvar
                                                                    px)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun c1
                                                                    ->
                                                                    match c1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    tannot ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ((Pulse_Syntax_Pure.wr
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    b q
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    (Pulse_RuntimeUtils.hnf_lax
                                                                    (Pulse_Typing.elab_env
                                                                    env1)
                                                                    tannot) x)))
                                                                    (Pulse_RuntimeUtils.union_ranges
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    b.Pulse_Syntax_Base.binder_ty)
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    (Pulse_RuntimeUtils.hnf_lax
                                                                    (Pulse_Typing.elab_env
                                                                    env1)
                                                                    tannot) x)))),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c1 x));
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    };
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.effect_tag)
                                                                    }))))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (36)))))
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
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Unexpected type of abstraction: "
                                                                    (Prims.strcat
                                                                    uu___3 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (prog.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match annot
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (prog.Pulse_Syntax_Base.range1))
                                                                    "Unannotated function body")
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ((Pulse_Syntax_Pure.wr
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    b q c)
                                                                    (Pulse_RuntimeUtils.union_ranges
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    b.Pulse_Syntax_Base.binder_ty)
                                                                    (range_of_comp
                                                                    c))),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.effect_tag)
                                                                    }))))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                             uu___1))) uu___1)))
                                       uu___1))) uu___1))) uu___)
let (qualifier_compat :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
        FStar_Reflection_V2_Data.aqualv ->
          (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun r ->
               fun q ->
                 fun q' ->
                   match (q, q') with
                   | (FStar_Pervasives_Native.None,
                      FStar_Reflection_V2_Data.Q_Explicit) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> ())))
                   | (FStar_Pervasives_Native.Some
                      (Pulse_Syntax_Base.Implicit),
                      FStar_Reflection_V2_Data.Q_Implicit) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> ())))
                   | (FStar_Pervasives_Native.Some
                      (Pulse_Syntax_Base.Implicit),
                      FStar_Reflection_V2_Data.Q_Meta uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> ())))
                   | (FStar_Pervasives_Native.Some (Pulse_Syntax_Base.TcArg),
                      FStar_Reflection_V2_Data.Q_Meta uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> ())))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (Pulse_Typing_Env.fail g
                               (FStar_Pervasives_Native.Some r)
                               "Unexpected binder qualifier"))) uu___3 uu___2
            uu___1 uu___
let rec (rebuild_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      FStar_Tactics_NamedView.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun annot ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (127)) (Prims.of_int (4))
                   (Prims.of_int (129)) (Prims.of_int (41)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (130)) (Prims.of_int (4))
                   (Prims.of_int (179)) (Prims.of_int (47)))))
          (Obj.magic
             (debug_abs g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                              (Prims.of_int (129)) (Prims.of_int (16))
                              (Prims.of_int (129)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                              (Prims.of_int (127)) (Prims.of_int (26))
                              (Prims.of_int (129)) (Prims.of_int (40)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.term_to_string annot))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Abs.fst"
                                         (Prims.of_int (127))
                                         (Prims.of_int (26))
                                         (Prims.of_int (129))
                                         (Prims.of_int (40)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Abs.fst"
                                         (Prims.of_int (127))
                                         (Prims.of_int (26))
                                         (Prims.of_int (129))
                                         (Prims.of_int (40)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Abs.fst"
                                               (Prims.of_int (128))
                                               (Prims.of_int (16))
                                               (Prims.of_int (128))
                                               (Prims.of_int (39)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (122))
                                               (Prims.of_int (8))
                                               (Prims.of_int (124))
                                               (Prims.of_int (44)))))
                                      (Obj.magic
                                         (Pulse_Syntax_Printer.st_term_to_string
                                            t))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              fun x ->
                                                Prims.strcat
                                                  (Prims.strcat
                                                     "rebuild_abs\n\t"
                                                     (Prims.strcat uu___2
                                                        "\n\t"))
                                                  (Prims.strcat x "\n")))))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))))
          (fun uu___ ->
             (fun uu___ ->
                match ((t.Pulse_Syntax_Base.term1),
                        (FStar_Reflection_V2_Builtins.inspect_ln annot))
                with
                | (Pulse_Syntax_Base.Tm_Abs
                   { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                     Pulse_Syntax_Base.ascription = asc;
                     Pulse_Syntax_Base.body = body;_},
                   FStar_Reflection_V2_Data.Tv_Arrow (b', c')) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (132)) (Prims.of_int (15))
                                  (Prims.of_int (132)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (133)) (Prims.of_int (6))
                                  (Prims.of_int (173)) (Prims.of_int (41)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_V2_Builtins.inspect_binder b'))
                         (fun uu___1 ->
                            (fun b'1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (133))
                                             (Prims.of_int (6))
                                             (Prims.of_int (133))
                                             (Prims.of_int (56)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (133))
                                             (Prims.of_int (57))
                                             (Prims.of_int (173))
                                             (Prims.of_int (41)))))
                                    (Obj.magic
                                       (qualifier_compat g
                                          (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.range
                                          q b'1.FStar_Reflection_V2_Data.qual))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Abs.fst"
                                                        (Prims.of_int (134))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (134))
                                                        (Prims.of_int (22)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Abs.fst"
                                                        (Prims.of_int (134))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (173))
                                                        (Prims.of_int (41)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     b'1.FStar_Reflection_V2_Data.sort2))
                                               (fun uu___2 ->
                                                  (fun ty ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Abs.fst"
                                                                   (Prims.of_int (135))
                                                                   (Prims.of_int (17))
                                                                   (Prims.of_int (135))
                                                                   (Prims.of_int (34)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Abs.fst"
                                                                   (Prims.of_int (136))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (173))
                                                                   (Prims.of_int (41)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                FStar_Reflection_V2_Builtins.inspect_comp
                                                                  c'))
                                                          (fun uu___2 ->
                                                             (fun comp ->
                                                                match comp
                                                                with
                                                                | FStar_Reflection_V2_Data.C_Total
                                                                    res_ty ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Abs
                                                                    body.Pulse_Syntax_Base.term1
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.mk_binder_with_attrs
                                                                    ty
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    b.Pulse_Syntax_Base.binder_attrs))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun b1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (rebuild_abs
                                                                    g body
                                                                    res_ty))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b1;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    (asc.Pulse_Syntax_Base.annotated);
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    };
                                                                    Pulse_Syntax_Base.body
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (t.Pulse_Syntax_Base.effect_tag)
                                                                    }))))
                                                                    uu___2))
                                                                    else
                                                                    Obj.repr
                                                                    (match 
                                                                    Pulse_Readback.readback_comp
                                                                    res_ty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    res_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Expected a computation type; got "
                                                                    (Prims.strcat
                                                                    uu___3 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    res_ty))
                                                                    uu___3))
                                                                    uu___3))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    ty1) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.inspect
                                                                    res_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_Arrow
                                                                    (b1,
                                                                    uu___4)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (91)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.binder_to_string
                                                                    b1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Expected a binder for "
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___5))
                                                                    uu___5))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (51)))))
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
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    ty1)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Incorrect annotation on function body, expected a stateful computation type; got: "
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___5))
                                                                    uu___5)))
                                                                    uu___3))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    (Pulse_Syntax_Base.mk_binder_with_attrs
                                                                    ty
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    b.Pulse_Syntax_Base.binder_attrs);
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    (asc.Pulse_Syntax_Base.annotated);
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    c)
                                                                    };
                                                                    Pulse_Syntax_Base.body
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (t.Pulse_Syntax_Base.effect_tag)
                                                                    })))))
                                                                | uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (173))
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
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    annot))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Unexpected type of abstraction: "
                                                                    (Prims.strcat
                                                                    uu___3 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3))))
                                                               uu___2)))
                                                    uu___2))) uu___1)))
                              uu___1))
                | uu___1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (178)) (Prims.of_int (16))
                                  (Prims.of_int (179)) (Prims.of_int (47)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (177)) (Prims.of_int (6))
                                  (Prims.of_int (179)) (Prims.of_int (47)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Abs.fst"
                                        (Prims.of_int (179))
                                        (Prims.of_int (22))
                                        (Prims.of_int (179))
                                        (Prims.of_int (46)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))))
                               (Obj.magic
                                  (FStar_Tactics_V2_Builtins.term_to_string
                                     annot))
                               (fun uu___2 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       Prims.strcat
                                         "Unexpected arity of abstraction: expected a term of type "
                                         (Prims.strcat uu___2 "")))))
                         (fun uu___2 ->
                            (fun uu___2 ->
                               Obj.magic
                                 (Pulse_Typing_Env.fail g
                                    (FStar_Pervasives_Native.Some
                                       (t.Pulse_Syntax_Base.range1)) uu___2))
                              uu___2))) uu___)
let (preprocess_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (185)) (Prims.of_int (19))
                 (Prims.of_int (185)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (185)) (Prims.of_int (3)) (Prims.of_int (190))
                 (Prims.of_int (7))))) (Obj.magic (arrow_of_abs g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (annot, t1) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (186)) (Prims.of_int (4))
                                (Prims.of_int (186)) (Prims.of_int (88)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (186)) (Prims.of_int (89))
                                (Prims.of_int (190)) (Prims.of_int (7)))))
                       (Obj.magic
                          (debug_abs g
                             (fun uu___1 ->
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (186))
                                           (Prims.of_int (63))
                                           (Prims.of_int (186))
                                           (Prims.of_int (87)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (590))
                                           (Prims.of_int (19))
                                           (Prims.of_int (590))
                                           (Prims.of_int (31)))))
                                  (Obj.magic
                                     (Pulse_Syntax_Printer.term_to_string
                                        annot))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          Prims.strcat "arrow_of_abs = "
                                            (Prims.strcat uu___2 "\n"))))))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (187))
                                           (Prims.of_int (19))
                                           (Prims.of_int (187))
                                           (Prims.of_int (72)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (186))
                                           (Prims.of_int (89))
                                           (Prims.of_int (190))
                                           (Prims.of_int (7)))))
                                  (Obj.magic
                                     (Pulse_Checker_Pure.instantiate_term_implicits
                                        g annot))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        match uu___2 with
                                        | (annot1, uu___3) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Abs.fst"
                                                          (Prims.of_int (188))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (188))
                                                          (Prims.of_int (35)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Abs.fst"
                                                          (Prims.of_int (189))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (190))
                                                          (Prims.of_int (7)))))
                                                 (Obj.magic
                                                    (rebuild_abs g t1 annot1))
                                                 (fun uu___4 ->
                                                    (fun abs ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (88)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (11)))))
                                                            (Obj.magic
                                                               (debug_abs g
                                                                  (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    abs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "rebuild_abs = "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\n"))))))
                                                            (fun uu___4 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    -> abs))))
                                                      uu___4))) uu___2)))
                            uu___1))) uu___)
let sub_effect_comp :
  'uuuuu .
    Pulse_Typing_Env.env ->
      'uuuuu ->
        Pulse_Syntax_Base.comp_ascription ->
          Pulse_Syntax_Base.comp ->
            ((Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.lift_comp) Prims.dtuple2
               FStar_Pervasives_Native.option,
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun r ->
               fun asc ->
                 fun c_computed ->
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           match asc.Pulse_Syntax_Base.elaborated with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some c ->
                               (match (c_computed, c) with
                                | (Pulse_Syntax_Base.C_Tot t1,
                                   Pulse_Syntax_Base.C_Tot t2) ->
                                    FStar_Pervasives_Native.None
                                | (Pulse_Syntax_Base.C_ST uu___1,
                                   Pulse_Syntax_Base.C_ST uu___2) ->
                                    FStar_Pervasives_Native.None
                                | (Pulse_Syntax_Base.C_STGhost
                                   (uu___1, uu___2),
                                   Pulse_Syntax_Base.C_STGhost
                                   (uu___3, uu___4)) ->
                                    FStar_Pervasives_Native.None
                                | (Pulse_Syntax_Base.C_STAtomic
                                   (i, Pulse_Syntax_Base.Neutral, c1),
                                   Pulse_Syntax_Base.C_STGhost
                                   (uu___1, uu___2)) ->
                                    FStar_Pervasives_Native.Some
                                      (Prims.Mkdtuple2
                                         ((Pulse_Syntax_Base.C_STGhost
                                             (i, c1)),
                                           (Pulse_Typing.Lift_Neutral_Ghost
                                              (g, c_computed))))
                                | (Pulse_Syntax_Base.C_STAtomic (i, o1, c1),
                                   Pulse_Syntax_Base.C_STAtomic (j, o2, c2))
                                    ->
                                    if Pulse_Typing.sub_observability o1 o2
                                    then
                                      FStar_Pervasives_Native.Some
                                        (Prims.Mkdtuple2
                                           ((Pulse_Syntax_Base.C_STAtomic
                                               (i, o2, c1)),
                                             (Pulse_Typing.Lift_Observability
                                                (g, c_computed, o2))))
                                    else FStar_Pervasives_Native.None
                                | uu___1 -> FStar_Pervasives_Native.None))))
            uu___3 uu___2 uu___1 uu___
let (check_effect_annotation :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.comp_ascription ->
        Pulse_Syntax_Base.comp ->
          ((Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_sub)
             Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r ->
      fun asc ->
        fun c_computed ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                     (Prims.of_int (214)) (Prims.of_int (12))
                     (Prims.of_int (214)) (Prims.of_int (42)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                     (Prims.of_int (215)) (Prims.of_int (2))
                     (Prims.of_int (264)) (Prims.of_int (7)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  Prims.Mkdtuple2
                    (c_computed, (Pulse_Typing.STS_Refl (g, c_computed)))))
            (fun uu___ ->
               (fun nop ->
                  match asc.Pulse_Syntax_Base.elaborated with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> nop)))
                  | FStar_Pervasives_Native.Some c ->
                      Obj.magic
                        (Obj.repr
                           (match (c, c_computed) with
                            | (Pulse_Syntax_Base.C_Tot uu___,
                               Pulse_Syntax_Base.C_Tot uu___1) ->
                                Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> nop))
                            | (Pulse_Syntax_Base.C_ST uu___,
                               Pulse_Syntax_Base.C_ST uu___1) ->
                                Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> nop))
                            | (Pulse_Syntax_Base.C_STGhost (i, c1),
                               Pulse_Syntax_Base.C_STGhost (j, c2)) ->
                                Obj.repr
                                  (if Pulse_Syntax_Base.eq_tm i j
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ -> nop))
                                   else
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (50)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (53))
                                                   (Prims.of_int (255))
                                                   (Prims.of_int (20)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                Pulse_Syntax_Base.mk_binder
                                                  "res" FStar_Range.range_0
                                                  c2.Pulse_Syntax_Base.res))
                                          (fun uu___1 ->
                                             (fun b ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (255))
                                                              (Prims.of_int (20)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Pulse_Typing.tm_inames_subset
                                                             j i))
                                                     (fun uu___1 ->
                                                        (fun phi ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (48)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    typing ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.with_policy
                                                                    FStar_Tactics_Types.ForceSMT
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Checker_Pure.try_check_prop_validity
                                                                    g phi ())))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun tok
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    tok
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Annotated effect expects only invariants in")
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    j))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "to be opened; but computed effect claims that invariants")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___2
                                                                    (Pulse_PP.text
                                                                    "are opened")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    [uu___1]))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    i))
                                                                    uu___1))
                                                                    uu___1)))
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
                                                                    match tok
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((match c_computed
                                                                    with
                                                                    | Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___3,
                                                                    obs,
                                                                    uu___4)
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, c2,
                                                                    j, i,
                                                                    obs, obs,
                                                                    ())
                                                                    | Pulse_Syntax_Base.C_STGhost
                                                                    (uu___3,
                                                                    uu___4)
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    (g, c2,
                                                                    j, i, ()))))))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                            | (Pulse_Syntax_Base.C_STAtomic
                               (i, Pulse_Syntax_Base.Observable, c1),
                               Pulse_Syntax_Base.C_STAtomic
                               (j, Pulse_Syntax_Base.Observable, c2)) ->
                                Obj.repr
                                  (if Pulse_Syntax_Base.eq_tm i j
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ -> nop))
                                   else
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (50)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (233))
                                                   (Prims.of_int (53))
                                                   (Prims.of_int (255))
                                                   (Prims.of_int (20)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                Pulse_Syntax_Base.mk_binder
                                                  "res" FStar_Range.range_0
                                                  c2.Pulse_Syntax_Base.res))
                                          (fun uu___1 ->
                                             (fun b ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (255))
                                                              (Prims.of_int (20)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Pulse_Typing.tm_inames_subset
                                                             j i))
                                                     (fun uu___1 ->
                                                        (fun phi ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (48)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    typing ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.with_policy
                                                                    FStar_Tactics_Types.ForceSMT
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Checker_Pure.try_check_prop_validity
                                                                    g phi ())))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun tok
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    tok
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Annotated effect expects only invariants in")
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    j))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "to be opened; but computed effect claims that invariants")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___2
                                                                    (Pulse_PP.text
                                                                    "are opened")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    [uu___1]))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    i))
                                                                    uu___1))
                                                                    uu___1)))
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
                                                                    match tok
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((match c_computed
                                                                    with
                                                                    | Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___3,
                                                                    obs,
                                                                    uu___4)
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, c2,
                                                                    j, i,
                                                                    obs, obs,
                                                                    ())
                                                                    | Pulse_Syntax_Base.C_STGhost
                                                                    (uu___3,
                                                                    uu___4)
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    (g, c2,
                                                                    j, i, ()))))))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                            | (uu___, uu___1) ->
                                Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (259))
                                              (Prims.of_int (26))
                                              (Prims.of_int (264))
                                              (Prims.of_int (7)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (259))
                                              (Prims.of_int (6))
                                              (Prims.of_int (264))
                                              (Prims.of_int (7)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Abs.fst"
                                                    (Prims.of_int (260))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (263))
                                                    (Prims.of_int (67)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Abs.fst"
                                                    (Prims.of_int (259))
                                                    (Prims.of_int (26))
                                                    (Prims.of_int (264))
                                                    (Prims.of_int (7)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Abs.fst"
                                                          (Prims.of_int (260))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (261))
                                                          (Prims.of_int (58)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Abs.fst"
                                                          (Prims.of_int (260))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (263))
                                                          (Prims.of_int (67)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (261))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (261))
                                                                (Prims.of_int (58)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (260))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (261))
                                                                (Prims.of_int (58)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (57)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (58)))))
                                                             (Obj.magic
                                                                (Pulse_Syntax_Printer.tag_of_comp
                                                                   c))
                                                             (fun uu___2 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    FStar_Pprint.arbitrary_string
                                                                    uu___2))))
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___3 ->
                                                               FStar_Pprint.prefix
                                                                 (Prims.of_int (4))
                                                                 Prims.int_one
                                                                 (Pulse_PP.text
                                                                    "Expected effect")
                                                                 uu___2))))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (67)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (67)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (67)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (67)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.tag_of_comp
                                                                    c_computed))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.arbitrary_string
                                                                    uu___3))))
                                                                  (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "but this function body has effect")
                                                                    uu___3))))
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___2
                                                                    uu___3))))
                                                      uu___2)))
                                           (fun uu___2 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 -> [uu___2]))))
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           Obj.magic
                                             (Pulse_Typing_Env.fail_doc g
                                                (FStar_Pervasives_Native.Some
                                                   r) uu___2)) uu___2)))))
                 uu___)
let (maybe_rewrite_body_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.comp_ascription ->
            ((Pulse_Syntax_Base.comp,
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
                   fun d ->
                     fun asc ->
                       match asc.Pulse_Syntax_Base.annotated with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ -> Prims.Mkdtuple2 (c, d))))
                       | FStar_Pervasives_Native.Some
                           (Pulse_Syntax_Base.C_Tot t) ->
                           Obj.magic
                             (Obj.repr
                                (match c with
                                 | Pulse_Syntax_Base.C_Tot t' ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (278))
                                                (Prims.of_int (19))
                                                (Prims.of_int (278))
                                                (Prims.of_int (68)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (277))
                                                (Prims.of_int (20))
                                                (Prims.of_int (291))
                                                (Prims.of_int (7)))))
                                       (Obj.magic
                                          (Pulse_Checker_Pure.instantiate_term_implicits
                                             g t))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             match uu___ with
                                             | (t1, uu___1) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Abs.fst"
                                                               (Prims.of_int (279))
                                                               (Prims.of_int (32))
                                                               (Prims.of_int (279))
                                                               (Prims.of_int (69)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Abs.fst"
                                                               (Prims.of_int (278))
                                                               (Prims.of_int (71))
                                                               (Prims.of_int (290))
                                                               (Prims.of_int (26)))))
                                                      (Obj.magic
                                                         (Pulse_Checker_Pure.check_universe
                                                            g t1))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            match uu___2 with
                                                            | Prims.Mkdtuple2
                                                                (u, t_typing)
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.norm_st_typing_inverse
                                                                    g e t' d
                                                                    u t1 ()
                                                                    [FStar_Pervasives.hnf;
                                                                    FStar_Pervasives.delta]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    "Inferred type is incompatible with annotation")
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (debug_abs
                                                                    g
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    t1)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (288))
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
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "maybe_rewrite_body_typing:{\nfrom "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "\nto "))
                                                                    (Prims.strcat
                                                                    x "}\n")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_Tot
                                                                    t1), d1)))))
                                                                    uu___3)))
                                                           uu___2))) uu___)
                                 | uu___ ->
                                     Pulse_Typing_Env.fail g
                                       (FStar_Pervasives_Native.Some
                                          (e.Pulse_Syntax_Base.range1))
                                       "Inferred type is incompatible with annotation"))
                       | FStar_Pervasives_Native.Some c1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Abs.fst"
                                            (Prims.of_int (296))
                                            (Prims.of_int (15))
                                            (Prims.of_int (296))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Abs.fst"
                                            (Prims.of_int (297))
                                            (Prims.of_int (6))
                                            (Prims.of_int (297))
                                            (Prims.of_int (92)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         Pulse_Syntax_Base.st_comp_of_comp c1))
                                   (fun uu___ ->
                                      (fun st ->
                                         Obj.magic
                                           (Pulse_Typing_Env.fail g
                                              (FStar_Pervasives_Native.Some
                                                 (Pulse_RuntimeUtils.range_of_term
                                                    st.Pulse_Syntax_Base.pre))
                                              "Unexpected annotation on a function body"))
                                        uu___)))) uu___4 uu___3 uu___2 uu___1
              uu___
let (open_ascription :
  Pulse_Syntax_Base.comp_ascription ->
    Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.comp_ascription)
  =
  fun c ->
    fun nv ->
      let t = Pulse_Syntax_Pure.term_of_nvar nv in
      Pulse_Syntax_Naming.subst_ascription c
        [FStar_Reflection_Typing.DT (Prims.int_zero, t)]
let (close_ascription :
  Pulse_Syntax_Base.comp_ascription ->
    Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.comp_ascription)
  =
  fun c ->
    fun nv ->
      Pulse_Syntax_Naming.subst_ascription c
        [FStar_Reflection_Typing.ND
           ((FStar_Pervasives_Native.snd nv), Prims.int_zero)]
let rec (check_abs_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Checker_Base.check_t ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun check ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (312)) (Prims.of_int (14))
                   (Prims.of_int (312)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (313)) (Prims.of_int (2))
                   (Prims.of_int (430)) (Prims.of_int (29)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> t.Pulse_Syntax_Base.range1))
          (fun uu___ ->
             (fun range ->
                match t.Pulse_Syntax_Base.term1 with
                | Pulse_Syntax_Base.Tm_Abs
                    {
                      Pulse_Syntax_Base.b =
                        { Pulse_Syntax_Base.binder_ty = t1;
                          Pulse_Syntax_Base.binder_ppname = ppname;
                          Pulse_Syntax_Base.binder_attrs = binder_attrs;_};
                      Pulse_Syntax_Base.q = qual;
                      Pulse_Syntax_Base.ascription = asc;
                      Pulse_Syntax_Base.body = body;_}
                    ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (316)) (Prims.of_int (24))
                                  (Prims.of_int (316)) (Prims.of_int (49)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (314)) (Prims.of_int (99))
                                  (Prims.of_int (430)) (Prims.of_int (29)))))
                         (Obj.magic
                            (Pulse_Checker_Pure.compute_tot_term_type g t1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | FStar_Pervasives.Mkdtuple3
                                   (t2, uu___1, uu___2) ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (317))
                                                 (Prims.of_int (28))
                                                 (Prims.of_int (317))
                                                 (Prims.of_int (46)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (316))
                                                 (Prims.of_int (52))
                                                 (Prims.of_int (430))
                                                 (Prims.of_int (29)))))
                                        (Obj.magic
                                           (Pulse_Checker_Pure.check_universe
                                              g t2))
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              match uu___3 with
                                              | Prims.Mkdtuple2 (u, t_typing)
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (318))
                                                                (Prims.of_int (12))
                                                                (Prims.of_int (318))
                                                                (Prims.of_int (19)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (318))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (430))
                                                                (Prims.of_int (29)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             Pulse_Typing_Env.fresh
                                                               g))
                                                       (fun uu___4 ->
                                                          (fun x ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (22)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ppname,
                                                                    x)))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun var
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    ppname t2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    open_ascription
                                                                    asc px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun asc1
                                                                    ->
                                                                    match 
                                                                    body_opened.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check_abs_core
                                                                    g'
                                                                    body_opened
                                                                    check))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (sub_effect_comp
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    asc1
                                                                    c_body))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body,
                                                                    body_typing)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    lift)) ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    (Pulse_Typing.T_Lift
                                                                    (g',
                                                                    body1,
                                                                    c_body,
                                                                    c_body1,
                                                                    body_typing,
                                                                    lift)))))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    body_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check_effect_annotation
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    asc1
                                                                    c_body1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body2,
                                                                    d_sub) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g',
                                                                    body1,
                                                                    c_body1,
                                                                    c_body2,
                                                                    body_typing1,
                                                                    d_sub)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    body_typing2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (maybe_rewrite_body_typing
                                                                    g' body1
                                                                    c_body2
                                                                    body_typing2
                                                                    asc1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body3,
                                                                    body_typing3)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    body1 x))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    body_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    binder_attrs))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun attr
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g attr))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___11)))
                                                                    uu___10))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Sealed.seal
                                                                    uu___10))))
                                                                    (fun
                                                                    binder_attrs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    FStar_Pervasives_Native.None
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs1
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    body_closed
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs1
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body3 x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs1
                                                                    }, u,
                                                                    body_closed,
                                                                    c_body3,
                                                                    (),
                                                                    body_typing3)))))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (match 
                                                                    asc1.Pulse_Syntax_Base.elaborated
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    "Missing annotation on a function body"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    r) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (52)))))
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
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    r)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Incorrect annotation on a function, expected a computation type, got: "
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___5))
                                                                    uu___5)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (c,
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c) px),
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_C_STAtomic
                                                                    c
                                                                    then
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c) px
                                                                    else
                                                                    Pulse_Syntax_Pure.tm_emp_inames),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c) px)),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) var
                                                                    Prims.int_one)))))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (elab_c,
                                                                    pre_opened,
                                                                    inames_opened,
                                                                    ret_ty,
                                                                    post_hint_body)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
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
                                                                    pre_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    pre_opened1
                                                                    x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (match post_hint_body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    [
                                                                    Pulse_PP.text
                                                                    "Top-level functions must be annotated with pre and post conditions"])
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.intro_post_hint
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "post_hint_typing"
                                                                    range g')
                                                                    (Pulse_Syntax_Base.effect_annot_of_comp
                                                                    elab_c)
                                                                    ret_ty
                                                                    post))
                                                                    (fun
                                                                    post_hint_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    post_hint_typing))))
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
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_fret"))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    ppname_ret
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    pre_opened1
                                                                    () post
                                                                    ppname_ret
                                                                    body_opened))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g'
                                                                    pre_opened1
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post) r
                                                                    ppname_ret))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_comp_nv
                                                                    elab_c px))
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    c_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (sub_effect_comp
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    c_opened
                                                                    c_body))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body,
                                                                    body_typing)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    lift)) ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    (Pulse_Typing.T_Lift
                                                                    (g',
                                                                    body1,
                                                                    c_body,
                                                                    c_body1,
                                                                    body_typing,
                                                                    lift)))))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    body_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> uu___9))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check_effect_annotation
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    c_opened
                                                                    c_body1))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body2,
                                                                    d_sub) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g',
                                                                    body1,
                                                                    c_body1,
                                                                    c_body2,
                                                                    body_typing1,
                                                                    d_sub)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    body_typing2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (maybe_rewrite_body_typing
                                                                    g' body1
                                                                    c_body2
                                                                    body_typing2
                                                                    asc1))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body3,
                                                                    body_typing3)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    FStar_Pervasives_Native.None
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body3 x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs
                                                                    }, u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x),
                                                                    c_body3,
                                                                    (),
                                                                    body_typing3)))))))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                            uu___4))) uu___3)))
                              uu___))) uu___)
let (check_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Checker_Base.check_t ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun check ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (434)) (Prims.of_int (10))
                   (Prims.of_int (434)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (435)) (Prims.of_int (2))
                   (Prims.of_int (435)) (Prims.of_int (26)))))
          (Obj.magic (preprocess_abs g t))
          (fun uu___ ->
             (fun t1 -> Obj.magic (check_abs_core g t1 check)) uu___)