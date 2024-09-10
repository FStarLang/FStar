open Prims
let (debug_main :
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
               "pulse.main"
           then
             Obj.magic
               (Obj.repr
                  (let uu___ = s () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (36)) (Prims.of_int (15))
                              (Prims.of_int (36)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (36)) (Prims.of_int (7))
                              (Prims.of_int (36)) (Prims.of_int (21)))))
                     (Obj.magic uu___)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___1))
                          uu___1)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let rec (mk_abs :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.binder * Pulse_Syntax_Base.bv) Prims.list ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun qbs ->
      fun body ->
        fun comp ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    fun s ->
                      fun r ->
                        {
                          Pulse_Syntax_Base.term1 = s;
                          Pulse_Syntax_Base.range1 = r;
                          Pulse_Syntax_Base.effect_tag =
                            Pulse_Syntax_Base.default_effect_hint
                        })) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (44))
                     (Prims.of_int (6)) (Prims.of_int (44))
                     (Prims.of_int (59)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (46))
                     (Prims.of_int (2)) (Prims.of_int (55))
                     (Prims.of_int (81))))) (Obj.magic uu___)
            (fun uu___1 ->
               (fun with_range ->
                  match qbs with
                  | (q, last, last_bv)::[] ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 with_range
                                   (Pulse_Syntax_Builder.tm_abs last q
                                      {
                                        Pulse_Syntax_Base.annotated =
                                          (FStar_Pervasives_Native.Some
                                             (Pulse_Syntax_Naming.close_comp
                                                comp
                                                last_bv.Pulse_Syntax_Base.bv_index));
                                        Pulse_Syntax_Base.elaborated =
                                          FStar_Pervasives_Native.None
                                      }
                                      (Pulse_Syntax_Naming.close_st_term body
                                         last_bv.Pulse_Syntax_Base.bv_index))
                                   (Pulse_Syntax_Naming.close_st_term body
                                      last_bv.Pulse_Syntax_Base.bv_index).Pulse_Syntax_Base.range1)))
                  | (q, b, bv)::qbs1 ->
                      Obj.magic
                        (Obj.repr
                           (let uu___1 = mk_abs g qbs1 body comp in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (53))
                                       (Prims.of_int (15))
                                       (Prims.of_int (53))
                                       (Prims.of_int (37)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (55)) (Prims.of_int (4))
                                       (Prims.of_int (55))
                                       (Prims.of_int (81)))))
                              (Obj.magic uu___1)
                              (fun body1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      with_range
                                        (Pulse_Syntax_Builder.tm_abs b q
                                           Pulse_Syntax_Base.empty_ascription
                                           (Pulse_Syntax_Naming.close_st_term
                                              body1
                                              bv.Pulse_Syntax_Base.bv_index))
                                        (Pulse_Syntax_Naming.close_st_term
                                           body1
                                           bv.Pulse_Syntax_Base.bv_index).Pulse_Syntax_Base.range1)))))
                 uu___1)
let (mk_opaque_let_with_impl :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.name ->
      Prims.string ->
        unit ->
          FStar_Reflection_Types.typ ->
            FStar_Reflection_Types.term ->
              ((unit, unit) FStar_Reflection_Typing.sigelt_for, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun cur_module ->
                   fun nm ->
                     fun tm ->
                       fun ty ->
                         fun impl ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   (true,
                                     (FStar_Reflection_V2_Builtins.pack_sigelt
                                        (FStar_Reflection_V2_Data.Sg_Let
                                           (false,
                                             [FStar_Reflection_V2_Builtins.pack_lb
                                                {
                                                  FStar_Reflection_V2_Data.lb_fv
                                                    =
                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                       (FStar_List_Tot_Base.op_At
                                                          cur_module 
                                                          [nm]));
                                                  FStar_Reflection_V2_Data.lb_us
                                                    = [];
                                                  FStar_Reflection_V2_Data.lb_typ
                                                    = ty;
                                                  FStar_Reflection_V2_Data.lb_def
                                                    = impl
                                                }]))),
                                     FStar_Pervasives_Native.None)))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (set_impl :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.typ FStar_Pervasives_Native.option ->
      (unit, unit) FStar_Reflection_Typing.sigelt_for ->
        Prims.bool ->
          FStar_Reflection_Types.term ->
            (unit, unit) FStar_Reflection_Typing.sigelt_for)
  =
  fun g ->
    fun t ->
      fun se ->
        fun r ->
          fun impl ->
            let uu___ =
              FStar_Reflection_V2_Builtins.inspect_sigelt
                (FStar_Pervasives_Native.__proj__Mktuple3__item___2 se) in
            match uu___ with
            | FStar_Reflection_V2_Data.Sg_Let (false, lb::[]) ->
                let lb1 = FStar_Reflection_V2_Builtins.inspect_lb lb in
                let lb2 =
                  {
                    FStar_Reflection_V2_Data.lb_fv =
                      (lb1.FStar_Reflection_V2_Data.lb_fv);
                    FStar_Reflection_V2_Data.lb_us =
                      (lb1.FStar_Reflection_V2_Data.lb_us);
                    FStar_Reflection_V2_Data.lb_typ =
                      (lb1.FStar_Reflection_V2_Data.lb_typ);
                    FStar_Reflection_V2_Data.lb_def = impl
                  } in
                (true,
                  (FStar_Reflection_V2_Builtins.pack_sigelt
                     (FStar_Reflection_V2_Data.Sg_Let
                        (r, [FStar_Reflection_V2_Builtins.pack_lb lb2]))),
                  (FStar_Pervasives_Native.__proj__Mktuple3__item___3 se))
let (check_fndefn :
  Pulse_Syntax_Base.decl ->
    Pulse_Soundness_Common.stt_env ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          unit ->
            ((unit, unit) FStar_Reflection_Typing.dsl_tac_result_t, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun g ->
      fun expected_t ->
        fun pre ->
          fun pre_typing ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> d.Pulse_Syntax_Base.d)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (86)) (Prims.of_int (20))
                       (Prims.of_int (86)) (Prims.of_int (23)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (83)) Prims.int_one (Prims.of_int (197))
                       (Prims.of_int (5))))) (Obj.magic uu___)
              (fun uu___1 ->
                 (fun uu___1 ->
                    match uu___1 with
                    | Pulse_Syntax_Base.FnDefn fn_d ->
                        let uu___2 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  FStar_Pervasives_Native.fst
                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                       fn_d.Pulse_Syntax_Base.id))) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (87)) (Prims.of_int (16))
                                      (Prims.of_int (87)) (Prims.of_int (43)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (87)) (Prims.of_int (46))
                                      (Prims.of_int (197)) (Prims.of_int (5)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun nm_orig ->
                                   let uu___3 =
                                     if fn_d.Pulse_Syntax_Base.isrec
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (Pulse_Recursion.add_knot g
                                               d.Pulse_Syntax_Base.range2 d))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 -> d))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (89))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (91))
                                                 (Prims.of_int (10)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (92))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (197))
                                                 (Prims.of_int (5)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun d1 ->
                                              let uu___4 =
                                                Obj.magic
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___5 ->
                                                        d1.Pulse_Syntax_Base.d)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Main.fst"
                                                            (Prims.of_int (94))
                                                            (Prims.of_int (51))
                                                            (Prims.of_int (94))
                                                            (Prims.of_int (54)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Main.fst"
                                                            (Prims.of_int (92))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (197))
                                                            (Prims.of_int (5)))))
                                                   (Obj.magic uu___4)
                                                   (fun uu___5 ->
                                                      (fun uu___5 ->
                                                         match uu___5 with
                                                         | Pulse_Syntax_Base.FnDefn
                                                             {
                                                               Pulse_Syntax_Base.id
                                                                 = id;
                                                               Pulse_Syntax_Base.isrec
                                                                 = isrec;
                                                               Pulse_Syntax_Base.bs
                                                                 = bs;
                                                               Pulse_Syntax_Base.comp
                                                                 = comp;
                                                               Pulse_Syntax_Base.meas
                                                                 = meas;
                                                               Pulse_Syntax_Base.body7
                                                                 = body;_}
                                                             ->
                                                             let uu___6 =
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id))) in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (37)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                  (Obj.magic
                                                                    uu___6)
                                                                  (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    nm_aux ->
                                                                    let uu___7
                                                                    =
                                                                    if
                                                                    Prims.uu___is_Nil
                                                                    bs
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d1.Pulse_Syntax_Base.range2))
                                                                    "main: FnDefn does not have binders"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    mk_abs g
                                                                    bs body
                                                                    comp in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    body1.Pulse_Syntax_Base.range1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun rng
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    debug_main
                                                                    g
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    body1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "\nbody after mk_abs:\n"
                                                                    (Prims.strcat
                                                                    uu___14
                                                                    "\n")))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Checker_Abs.check_abs
                                                                    g body1
                                                                    Pulse_Checker.check in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body2,
                                                                    c,
                                                                    t_typing)
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Pulse_Checker_Prover_Util.debug_prover
                                                                    g
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Pulse_Syntax_Printer.comp_to_string
                                                                    c in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    body2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\ncheck call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___21
                                                                    "\nat type "))
                                                                    (Prims.strcat
                                                                    x "\n"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    uu___20
                                                                    uu___18))))
                                                                    uu___18)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    debug_main
                                                                    g
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    Pulse_Typing_Printer.print_st_typing
                                                                    g body2 c
                                                                    t_typing in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    body2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\nchecker call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___23
                                                                    "\nderivation="))
                                                                    (Prims.strcat
                                                                    x "\n"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    uu___22
                                                                    uu___20))))
                                                                    uu___20)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Pulse_Elaborate_Pure.elab_comp
                                                                    c)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    refl_t ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Pulse_RuntimeUtils.embed_st_term_for_extraction
                                                                    body2
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    refl_e ->
                                                                    let uu___21
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    ("pulse",
                                                                    refl_e))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun blob
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.ext_getv
                                                                    "pulse:elab_derivation" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    uu___24
                                                                    <> "")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    elab_derivation
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_module
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    cur_module
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    fun t ->
                                                                    fun se ->
                                                                    let uu___26
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    Pulse_Extract_CompilerLib.new_uenv
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun uenv
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    comp
                                                                    then
                                                                    let uu___27
                                                                    =
                                                                    Pulse_Extract_Main.extract_dv_ghost
                                                                    {
                                                                    Pulse_Extract_Main.uenv_inner
                                                                    = uenv;
                                                                    Pulse_Extract_Main.coreenv
                                                                    =
                                                                    (Pulse_Extract_CompilerLib.initial_core_env
                                                                    uenv)
                                                                    } body2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (122)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (122)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    set_impl
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) t se
                                                                    false
                                                                    uu___28)))
                                                                    else
                                                                    if
                                                                    fn_d.Pulse_Syntax_Base.isrec
                                                                    then
                                                                    (let uu___28
                                                                    =
                                                                    Pulse_Extract_Main.extract_dv_recursive
                                                                    {
                                                                    Pulse_Extract_Main.uenv_inner
                                                                    = uenv;
                                                                    Pulse_Extract_Main.coreenv
                                                                    =
                                                                    (Pulse_Extract_CompilerLib.initial_core_env
                                                                    uenv)
                                                                    } body2
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    (FStar_List_Tot_Base.append
                                                                    cur_module
                                                                    [nm_orig])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (154)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun impl
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    set_impl
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) t se
                                                                    true impl))))
                                                                    else
                                                                    (let uu___29
                                                                    =
                                                                    Pulse_Extract_Main.extract_pulse_dv
                                                                    uenv
                                                                    body2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    set_impl
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) t se
                                                                    false
                                                                    uu___30)))))
                                                                    uu___27))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    maybe_add_impl
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    fun
                                                                    refl_t1
                                                                    ->
                                                                    fun
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun nm
                                                                    ->
                                                                    if
                                                                    elab_derivation
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Reflection_Typing.mk_checked_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)
                                                                    cur_module
                                                                    nm
                                                                    (Pulse_Elaborate_Core.elab_st_typing
                                                                    g body2 c
                                                                    t_typing)
                                                                    refl_t1)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Reflection_Util.mk_opaque_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)
                                                                    cur_module
                                                                    nm ()
                                                                    refl_t1)))
                                                                    uu___29))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    mk_main_decl
                                                                    ->
                                                                    if
                                                                    fn_d.Pulse_Syntax_Base.isrec
                                                                    then
                                                                    let uu___26
                                                                    =
                                                                    mk_main_decl
                                                                    refl_t () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    main_decl
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    main_decl)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    main_decl1
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    main_decl1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    match uu___29
                                                                    with
                                                                    | 
                                                                    (chk, se,
                                                                    uu___30)
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    nm_orig)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun nm
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "pulse.recursive"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    (nm,
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    attribute
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Pulse_RuntimeUtils.add_attribute
                                                                    se
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "noextract_to"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "krml"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun se1
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Pulse_RuntimeUtils.add_noextract_qual
                                                                    se1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun se2
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Pulse_RuntimeUtils.add_attribute
                                                                    se2
                                                                    attribute)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun se3
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (chk,
                                                                    se3,
                                                                    (FStar_Pervasives_Native.Some
                                                                    blob)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    main_decl2
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    Pulse_Recursion.tie_knot
                                                                    g rng
                                                                    nm_orig
                                                                    nm_aux
                                                                    refl_t
                                                                    blob in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (fun
                                                                    recursive_decl
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    maybe_add_impl
                                                                    expected_t
                                                                    recursive_decl in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    ([main_decl2],
                                                                    uu___39,
                                                                    [])))))
                                                                    uu___38)))
                                                                    uu___37)))
                                                                    uu___36)))
                                                                    uu___35)))
                                                                    uu___34)))
                                                                    uu___33)))
                                                                    uu___32)))
                                                                    uu___29)))
                                                                    uu___28)))
                                                                    uu___27))
                                                                    else
                                                                    (let uu___27
                                                                    =
                                                                    match expected_t
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (refl_t,
                                                                    ()))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___28
                                                                    =
                                                                    Pulse_Checker_Pure.check_subtyping
                                                                    g refl_t
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun tok
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (t, ()))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (refl_t1,
                                                                    uu___29)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    uu___28)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    mk_main_decl
                                                                    refl_t1
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    main_decl
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    main_decl)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    match uu___34
                                                                    with
                                                                    | 
                                                                    (chk, se,
                                                                    uu___35)
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (chk, se,
                                                                    (FStar_Pervasives_Native.Some
                                                                    blob)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    main_decl1
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    maybe_add_impl
                                                                    expected_t
                                                                    main_decl1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    ([],
                                                                    uu___38,
                                                                    [])))))
                                                                    uu___37)))
                                                                    uu___34)))
                                                                    uu___33)))
                                                                    uu___31)))
                                                                    uu___28))))
                                                                    uu___26)))
                                                                    uu___25)))
                                                                    uu___24)))
                                                                    uu___23)))
                                                                    uu___22)))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                        uu___5))) uu___4)))
                                  uu___3))) uu___1)
let (check_fndecl :
  Pulse_Syntax_Base.decl ->
    Pulse_Soundness_Common.stt_env ->
      ((unit, unit) FStar_Reflection_Typing.dsl_tac_result_t, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun g ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> d.Pulse_Syntax_Base.d)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (204))
                 (Prims.of_int (32)) (Prims.of_int (204)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (203))
                 Prims.int_one (Prims.of_int (241)) (Prims.of_int (29)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | Pulse_Syntax_Base.FnDecl
                  { Pulse_Syntax_Base.id1 = id; Pulse_Syntax_Base.bs1 = bs;
                    Pulse_Syntax_Base.comp1 = comp;_}
                  ->
                  let uu___2 =
                    if Prims.uu___is_Nil bs
                    then
                      Obj.magic
                        (Obj.repr
                           (Pulse_Typing_Env.fail g
                              (FStar_Pervasives_Native.Some
                                 (d.Pulse_Syntax_Base.range2))
                              "main: FnDecl does not have binders"))
                    else
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 -> ()))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (205)) (Prims.of_int (2))
                                (Prims.of_int (206)) (Prims.of_int (62)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (206)) (Prims.of_int (63))
                                (Prims.of_int (241)) (Prims.of_int (29)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             let uu___4 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___5 ->
                                       FStar_Pervasives_Native.fst
                                         (FStar_Reflection_V2_Builtins.inspect_ident
                                            id))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (208))
                                           (Prims.of_int (11))
                                           (Prims.of_int (208))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (208))
                                           (Prims.of_int (36))
                                           (Prims.of_int (241))
                                           (Prims.of_int (29)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun nm ->
                                        let uu___5 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 ->
                                                  Pulse_Syntax_Base.st_comp_of_comp
                                                    comp)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (209))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (209))
                                                      (Prims.of_int (32)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (209))
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (241))
                                                      (Prims.of_int (29)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun stc ->
                                                   let uu___6 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___7 ->
                                                             {
                                                               Pulse_Syntax_Base.term1
                                                                 =
                                                                 (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    =
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    comp);
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (stc.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.typ
                                                                    =
                                                                    (stc.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                               Pulse_Syntax_Base.range1
                                                                 =
                                                                 (d.Pulse_Syntax_Base.range2);
                                                               Pulse_Syntax_Base.effect_tag
                                                                 =
                                                                 (FStar_Sealed.seal
                                                                    FStar_Pervasives_Native.None)
                                                             })) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (214))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (221))
                                                                 (Prims.of_int (27)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (223))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (241))
                                                                 (Prims.of_int (29)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           (fun body ->
                                                              let uu___7 =
                                                                mk_abs g bs
                                                                  body comp in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (34)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
                                                                   (Obj.magic
                                                                    uu___7)
                                                                   (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    body1.Pulse_Syntax_Base.range1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun rng
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Pulse_RuntimeUtils.with_extv
                                                                    "pulse:no_admit_diag"
                                                                    "1"
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Checker_Abs.check_abs
                                                                    g body1
                                                                    Pulse_Checker.check) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
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
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uu___11,
                                                                    c,
                                                                    t_typing)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Elaborate_Pure.elab_comp
                                                                    c)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun typ
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_module
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_List_Tot_Base.append
                                                                    uu___18
                                                                    [nm])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.nm1
                                                                    = uu___17;
                                                                    FStar_Tactics_NamedView.univs2
                                                                    = [];
                                                                    FStar_Tactics_NamedView.typ1
                                                                    = typ
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_NamedView.Sg_Val
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    uu___15))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun se
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    ([],
                                                                    (false,
                                                                    se,
                                                                    FStar_Pervasives_Native.None),
                                                                    [])))))
                                                                    uu___13)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                             uu___7))) uu___6)))
                                       uu___5))) uu___3))) uu___1)
let (main' :
  Pulse_Syntax_Base.decl ->
    Pulse_Syntax_Base.term ->
      FStar_Reflection_Typing.fstar_top_env ->
        Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
          ((unit, unit) FStar_Reflection_Typing.dsl_tac_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun d ->
             fun pre ->
               fun g ->
                 fun expected_t ->
                   match Pulse_Soundness_Common.check_top_level_environment g
                   with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_V2_Derived.fail
                               "pulse main: top-level environment does not include stt at the expected types"))
                   | FStar_Pervasives_Native.Some g1 ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ =
                               if
                                 Pulse_RuntimeUtils.debug_at_level
                                   (Pulse_Typing_Env.fstar_env g1) "Pulse"
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___1 =
                                         let uu___2 =
                                           Pulse_Syntax_Printer.decl_to_string
                                             d in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (249))
                                                    (Prims.of_int (67))
                                                    (Prims.of_int (249))
                                                    (Prims.of_int (87)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "prims.fst"
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic uu___2)
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   Prims.strcat
                                                     "About to check pulse decl:\n"
                                                     (Prims.strcat uu___3
                                                        "\n"))) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (249))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (249))
                                                  (Prims.of_int (88)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (249))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (249))
                                                  (Prims.of_int (88)))))
                                         (Obj.magic uu___1)
                                         (fun uu___2 ->
                                            (fun uu___2 ->
                                               Obj.magic
                                                 (FStar_Tactics_V2_Builtins.print
                                                    uu___2)) uu___2)))
                               else
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> ()))) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (248))
                                        (Prims.of_int (6))
                                        (Prims.of_int (249))
                                        (Prims.of_int (88)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (249))
                                        (Prims.of_int (89))
                                        (Prims.of_int (260))
                                        (Prims.of_int (82)))))
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     let uu___2 =
                                       Pulse_Checker_Pure.compute_tot_term_type
                                         g1 pre in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (250))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (250))
                                                   (Prims.of_int (84)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (249))
                                                   (Prims.of_int (89))
                                                   (Prims.of_int (260))
                                                   (Prims.of_int (82)))))
                                          (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (pre1, ty, pre_typing) ->
                                                    let uu___4 =
                                                      if
                                                        Prims.op_Negation
                                                          (Pulse_Syntax_Base.eq_tm
                                                             ty
                                                             Pulse_Syntax_Pure.tm_slprop)
                                                      then
                                                        Obj.magic
                                                          (Obj.repr
                                                             (Pulse_Typing_Env.fail
                                                                g1
                                                                (FStar_Pervasives_Native.Some
                                                                   (Pulse_RuntimeUtils.range_of_term
                                                                    pre1))
                                                                "pulse main: cannot typecheck pre at type slprop"))
                                                      else
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___6
                                                                   -> ()))) in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (251))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (252))
                                                                  (Prims.of_int (110)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (252))
                                                                  (Prims.of_int (111))
                                                                  (Prims.of_int (260))
                                                                  (Prims.of_int (82)))))
                                                         (Obj.magic uu___4)
                                                         (fun uu___5 ->
                                                            (fun uu___5 ->
                                                               let uu___6 =
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ())) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (62)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (82)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___6)
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    match 
                                                                    d.Pulse_Syntax_Base.d
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.FnDefn
                                                                    {
                                                                    Pulse_Syntax_Base.id
                                                                    = uu___7;
                                                                    Pulse_Syntax_Base.isrec
                                                                    = uu___8;
                                                                    Pulse_Syntax_Base.bs
                                                                    = uu___9;
                                                                    Pulse_Syntax_Base.comp
                                                                    = uu___10;
                                                                    Pulse_Syntax_Base.meas
                                                                    = uu___11;
                                                                    Pulse_Syntax_Base.body7
                                                                    = uu___12;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (check_fndefn
                                                                    d g1
                                                                    expected_t
                                                                    pre1 ())
                                                                    | 
                                                                    Pulse_Syntax_Base.FnDecl
                                                                    {
                                                                    Pulse_Syntax_Base.id1
                                                                    = uu___7;
                                                                    Pulse_Syntax_Base.bs1
                                                                    = uu___8;
                                                                    Pulse_Syntax_Base.comp1
                                                                    = uu___9;_}
                                                                    ->
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    expected_t
                                                                    then
                                                                    Obj.magic
                                                                    (check_fndecl
                                                                    d g1)
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d.Pulse_Syntax_Base.range2))
                                                                    "pulse main: expected type provided for a FnDecl?"))
                                                                    uu___7)))
                                                              uu___5)))
                                               uu___3))) uu___1)))) uu___3
            uu___2 uu___1 uu___
let (join_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        let uu___3 = FStar_Tactics_V2_Builtins.top_env () in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (266))
                   (Prims.of_int (23)) (Prims.of_int (266))
                   (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (266))
                   (Prims.of_int (5)) (Prims.of_int (266))
                   (Prims.of_int (48))))) (Obj.magic uu___3)
          (fun uu___4 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___5 ->
                  Pulse_RuntimeUtils.debug_at_level uu___4 "pulse.join")) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (266))
                 (Prims.of_int (5)) (Prims.of_int (266)) (Prims.of_int (48)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (266))
                 (Prims.of_int (2)) (Prims.of_int (267)) (Prims.of_int (35)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 ->
              if uu___3
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_V2_Builtins.dump
                        "PULSE: Goals before join"))
              else
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___5 -> ()))))
             uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (266))
               (Prims.of_int (2)) (Prims.of_int (267)) (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (267))
               (Prims.of_int (36)) (Prims.of_int (288)) (Prims.of_int (4)))))
      (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = FStar_Tactics_V2_Derived.smt_goals () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (270)) (Prims.of_int (18))
                          (Prims.of_int (270)) (Prims.of_int (30)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (271)) (Prims.of_int (2))
                          (Prims.of_int (288)) (Prims.of_int (4)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun smt_goals ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStar_Tactics_V2_Derived.goals () in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (271))
                                      (Prims.of_int (13))
                                      (Prims.of_int (271))
                                      (Prims.of_int (21)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (271))
                                      (Prims.of_int (12))
                                      (Prims.of_int (271))
                                      (Prims.of_int (34)))))
                             (Obj.magic uu___6)
                             (fun uu___7 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___8 ->
                                     FStar_List_Tot_Base.op_At uu___7
                                       smt_goals)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (271)) (Prims.of_int (12))
                                    (Prims.of_int (271)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (271)) (Prims.of_int (2))
                                    (Prims.of_int (271)) (Prims.of_int (34)))))
                           (Obj.magic uu___5)
                           (fun uu___6 ->
                              (fun uu___6 ->
                                 Obj.magic
                                   (FStar_Tactics_V2_Builtins.set_goals
                                      uu___6)) uu___6) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (271)) (Prims.of_int (2))
                                     (Prims.of_int (271)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (272)) (Prims.of_int (2))
                                     (Prims.of_int (288)) (Prims.of_int (4)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    FStar_Tactics_V2_Builtins.set_smt_goals
                                      [] in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (272))
                                                (Prims.of_int (2))
                                                (Prims.of_int (272))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (272))
                                                (Prims.of_int (19))
                                                (Prims.of_int (288))
                                                (Prims.of_int (4)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             let uu___8 =
                                               let uu___9 =
                                                 FStar_Tactics_V2_Derived.goals
                                                   () in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (273))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (273))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (273))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (273))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic uu___9)
                                                 (fun uu___10 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___11 ->
                                                         FStar_List_Tot_Base.length
                                                           uu___10)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (273))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (273))
                                                           (Prims.of_int (36)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (274))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (288))
                                                           (Prims.of_int (4)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     (fun n ->
                                                        let uu___9 =
                                                          let uu___10 =
                                                            FStar_Tactics_V2_Derived.repeat
                                                              FStar_Tactics_V2_Builtins.join in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22)))))
                                                            (Obj.magic
                                                               uu___10)
                                                            (fun uu___11 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___12
                                                                    -> ())) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                (fun uu___10
                                                                   ->
                                                                   let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_V2_Derived.goals
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.uu___is_Nil
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_SMT.get_rlimit
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    uu___16 +
                                                                    ((n -
                                                                    Prims.int_one)
                                                                    *
                                                                    (Prims.of_int (2))))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    rlimit ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_SMT.set_rlimit
                                                                    rlimit))
                                                                    uu___15)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> ()))))
                                                                    uu___13) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.top_env
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    uu___16
                                                                    "pulse.join")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    if
                                                                    uu___15
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.dump
                                                                    "PULSE: Goals after join"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    -> ()))))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> ()))))
                                                                    uu___12)))
                                                                  uu___10)))
                                                       uu___9))) uu___7)))
                                 uu___5))) uu___4))) uu___2)
let (parse_guard_policy :
  Prims.string ->
    (FStar_Tactics_Types.guard_policy, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun s ->
       match s with
       | "Goal" ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Tactics_Types.Goal))
       | "SMT" ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Tactics_Types.SMT))
       | "SMTSync" ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Tactics_Types.SMTSync))
       | "Force" ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Tactics_Types.Force))
       | "ForceSMT" ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Tactics_Types.ForceSMT))
       | uu___ ->
           Obj.magic
             (FStar_Tactics_V1_Derived.fail
                (Prims.strcat "Unknown guard policy: " s))) uu___
let (main :
  Pulse_Syntax_Base.decl ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun t ->
    fun pre ->
      fun uu___ ->
        match uu___ with
        | (g, expected_t) ->
            let uu___1 =
              FStar_Tactics_V2_Builtins.set_guard_policy
                FStar_Tactics_Types.ForceSMT in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (307)) (Prims.of_int (2))
                       (Prims.of_int (307)) (Prims.of_int (27)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (308)) (Prims.of_int (2))
                       (Prims.of_int (318)) (Prims.of_int (5)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStar_Tactics_V2_Builtins.ext_getv
                            "pulse:guard_policy" in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Main.fst"
                                   (Prims.of_int (308)) (Prims.of_int (5))
                                   (Prims.of_int (308)) (Prims.of_int (34)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Main.fst"
                                   (Prims.of_int (308)) (Prims.of_int (5))
                                   (Prims.of_int (308)) (Prims.of_int (40)))))
                          (Obj.magic uu___5)
                          (fun uu___6 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___7 -> uu___6 <> "")) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (308)) (Prims.of_int (5))
                                 (Prims.of_int (308)) (Prims.of_int (40)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (308)) (Prims.of_int (2))
                                 (Prims.of_int (309)) (Prims.of_int (73)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              if uu___5
                              then
                                Obj.magic
                                  (Obj.repr
                                     (let uu___6 =
                                        let uu___7 =
                                          FStar_Tactics_V2_Builtins.ext_getv
                                            "pulse:guard_policy" in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (309))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (309))
                                                   (Prims.of_int (72)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (309))
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (309))
                                                   (Prims.of_int (73)))))
                                          (Obj.magic uu___7)
                                          (fun uu___8 ->
                                             (fun uu___8 ->
                                                Obj.magic
                                                  (parse_guard_policy uu___8))
                                               uu___8) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (309))
                                                 (Prims.of_int (21))
                                                 (Prims.of_int (309))
                                                 (Prims.of_int (73)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (309))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (309))
                                                 (Prims.of_int (73)))))
                                        (Obj.magic uu___6)
                                        (fun uu___7 ->
                                           (fun uu___7 ->
                                              Obj.magic
                                                (FStar_Tactics_V2_Builtins.set_guard_policy
                                                   uu___7)) uu___7)))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 -> ())))) uu___5) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Main.fst"
                                  (Prims.of_int (308)) (Prims.of_int (2))
                                  (Prims.of_int (309)) (Prims.of_int (73)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Main.fst"
                                  (Prims.of_int (309)) (Prims.of_int (74))
                                  (Prims.of_int (318)) (Prims.of_int (5)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun uu___4 ->
                               let uu___5 = main' t pre g expected_t in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Main.fst"
                                             (Prims.of_int (311))
                                             (Prims.of_int (12))
                                             (Prims.of_int (311))
                                             (Prims.of_int (36)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Main.fst"
                                             (Prims.of_int (313))
                                             (Prims.of_int (2))
                                             (Prims.of_int (318))
                                             (Prims.of_int (5)))))
                                    (Obj.magic uu___5)
                                    (fun uu___6 ->
                                       (fun res ->
                                          let uu___6 =
                                            let uu___7 =
                                              let uu___8 =
                                                FStar_Tactics_V2_Builtins.ext_getv
                                                  "pulse:join" in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Main.fst"
                                                         (Prims.of_int (313))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (313))
                                                         (Prims.of_int (26)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Main.fst"
                                                         (Prims.of_int (313))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (313))
                                                         (Prims.of_int (32)))))
                                                (Obj.magic uu___8)
                                                (fun uu___9 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___10 ->
                                                        uu___9 = "1")) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (32)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (317))
                                                       (Prims.of_int (20)))))
                                              (Obj.magic uu___7)
                                              (fun uu___8 ->
                                                 (fun uu___8 ->
                                                    if uu___8
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (join_smt_goals ()))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___10 ->
                                                                 ()))))
                                                   uu___8) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Main.fst"
                                                        (Prims.of_int (313))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (317))
                                                        (Prims.of_int (20)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Main.fst"
                                                        (Prims.of_int (311))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (311))
                                                        (Prims.of_int (9)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___8 -> res))))
                                         uu___6))) uu___4))) uu___2)
let (check_pulse_core :
  (unit ->
     ((Pulse_Syntax_Base.decl,
        (Prims.string * FStar_Range.range) FStar_Pervasives_Native.option)
        FStar_Pervasives.either,
       unit) FStar_Tactics_Effect.tac_repr)
    -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun as_decl ->
    fun uu___ ->
      match uu___ with
      | (env, expected_t) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Tactics_V2_Builtins.ext_getv "pulse:dump_on_failure" in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (324)) (Prims.of_int (9))
                         (Prims.of_int (324)) (Prims.of_int (41)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (324)) (Prims.of_int (9))
                         (Prims.of_int (324)) (Prims.of_int (48)))))
                (Obj.magic uu___3)
                (fun uu___4 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___5 -> uu___4 <> "1")) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (324)) (Prims.of_int (9))
                       (Prims.of_int (324)) (Prims.of_int (48)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (324)) (Prims.of_int (6))
                       (Prims.of_int (325)) (Prims.of_int (33)))))
              (Obj.magic uu___2)
              (fun uu___3 ->
                 (fun uu___3 ->
                    if uu___3
                    then
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_V2_Builtins.set_dump_on_failure
                              false))
                    else
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___5 -> ())))) uu___3) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (324))
                     (Prims.of_int (6)) (Prims.of_int (325))
                     (Prims.of_int (33)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (326))
                     (Prims.of_int (6)) (Prims.of_int (342))
                     (Prims.of_int (36))))) (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 = as_decl () in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (326)) (Prims.of_int (12))
                                (Prims.of_int (326)) (Prims.of_int (22)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (326)) (Prims.of_int (6))
                                (Prims.of_int (342)) (Prims.of_int (36)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun uu___4 ->
                             match uu___4 with
                             | FStar_Pervasives.Inl decl ->
                                 Obj.magic
                                   (Obj.repr
                                      (main decl Pulse_Syntax_Pure.tm_emp
                                         (env, expected_t)))
                             | FStar_Pervasives.Inr
                                 (FStar_Pervasives_Native.None) ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_V2_Derived.fail
                                         "Pulse parser failed"))
                             | FStar_Pervasives.Inr
                                 (FStar_Pervasives_Native.Some (msg, range))
                                 ->
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               FStar_Tactics_V2_Builtins.range_to_string
                                                 range in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Main.fst"
                                                        (Prims.of_int (336))
                                                        (Prims.of_int (44))
                                                        (Prims.of_int (336))
                                                        (Prims.of_int (69)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Printf.fst"
                                                        (Prims.of_int (122))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (124))
                                                        (Prims.of_int (44)))))
                                               (Obj.magic uu___8)
                                               (fun uu___9 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___10 ->
                                                       fun x ->
                                                         Prims.strcat
                                                           (Prims.strcat ""
                                                              (Prims.strcat
                                                                 uu___9 ": "))
                                                           (Prims.strcat x ""))) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (336))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (336))
                                                      (Prims.of_int (74)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (336))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (336))
                                                      (Prims.of_int (74)))))
                                             (Obj.magic uu___7)
                                             (fun uu___8 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___9 -> uu___8 msg)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (336))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (336))
                                                    (Prims.of_int (74)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Issue.fsti"
                                                    (Prims.of_int (49))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (49))
                                                    (Prims.of_int (65)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   FStar_Issue.mk_issue_doc
                                                     "Error"
                                                     [FStar_Pprint.arbitrary_string
                                                        uu___7]
                                                     (FStar_Pervasives_Native.Some
                                                        range)
                                                     FStar_Pervasives_Native.None
                                                     [])) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (335))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (339))
                                                  (Prims.of_int (21)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (341))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (342))
                                                  (Prims.of_int (36)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            (fun i ->
                                               let uu___6 =
                                                 FStar_Tactics_V2_Builtins.log_issues
                                                   [i] in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (341))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (341))
                                                             (Prims.of_int (24)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (342))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (342))
                                                             (Prims.of_int (36)))))
                                                    (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       FStar_Tactics_V2_Derived.fail
                                                         "Pulse parser failed")))
                                              uu___6)))) uu___4))) uu___2)
let (check_pulse :
  Prims.string Prims.list ->
    (Prims.string * Prims.string) Prims.list ->
      Prims.string ->
        Prims.string ->
          Prims.int ->
            Prims.int -> Prims.string -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun namespaces ->
    fun module_abbrevs ->
      fun content ->
        fun file_name ->
          fun line ->
            fun col ->
              fun nm ->
                fun uu___ ->
                  match uu___ with
                  | (env, expected_t) ->
                      check_pulse_core
                        (fun uu___1 ->
                           (fun uu___1 ->
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      PulseSyntaxExtension_ASTBuilder.parse_pulse
                                        env namespaces module_abbrevs content
                                        file_name line col))) uu___1)
                        (env, expected_t)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse"
    (Prims.of_int (9))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_8
               "Pulse.Main.check_pulse (plugin)"
               (FStar_Tactics_Native.from_tactic_8 check_pulse)
               (FStar_Syntax_Embeddings.e_list
                  FStar_Syntax_Embeddings.e_string)
               (FStar_Syntax_Embeddings.e_list
                  (FStar_Syntax_Embeddings.e_tuple2
                     FStar_Syntax_Embeddings.e_string
                     FStar_Syntax_Embeddings.e_string))
               FStar_Syntax_Embeddings.e_string
               FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
               FStar_Syntax_Embeddings.e_int FStar_Syntax_Embeddings.e_string
               (FStar_Syntax_Embeddings.e_tuple2
                  FStar_Reflection_V2_Embeddings.e_env
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Reflection_V2_Embeddings.e_term))
               (FStar_Syntax_Embeddings.e_tuple3
                  (FStar_Syntax_Embeddings.e_list
                     (FStar_Syntax_Embeddings.e_tuple3
                        FStar_Syntax_Embeddings.e_bool
                        FStar_Reflection_V2_Embeddings.e_sigelt
                        (FStar_Syntax_Embeddings.e_option
                           (FStar_Syntax_Embeddings.e_tuple2
                              FStar_Syntax_Embeddings.e_string
                              FStar_Reflection_V2_Embeddings.e_term))))
                  (FStar_Syntax_Embeddings.e_tuple3
                     FStar_Syntax_Embeddings.e_bool
                     FStar_Reflection_V2_Embeddings.e_sigelt
                     (FStar_Syntax_Embeddings.e_option
                        (FStar_Syntax_Embeddings.e_tuple2
                           FStar_Syntax_Embeddings.e_string
                           FStar_Reflection_V2_Embeddings.e_term)))
                  (FStar_Syntax_Embeddings.e_list
                     (FStar_Syntax_Embeddings.e_tuple3
                        FStar_Syntax_Embeddings.e_bool
                        FStar_Reflection_V2_Embeddings.e_sigelt
                        (FStar_Syntax_Embeddings.e_option
                           (FStar_Syntax_Embeddings.e_tuple2
                              FStar_Syntax_Embeddings.e_string
                              FStar_Reflection_V2_Embeddings.e_term))))) psc
               ncb us args)
let check_pulse_after_desugar : 'a . 'a -> FStar_Reflection_Typing.dsl_tac_t
  =
  fun decl ->
    fun uu___ ->
      match uu___ with
      | (env, expected_t) ->
          check_pulse_core
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          FStar_Pervasives.Inl
                            (Pulse_RuntimeUtils.unembed_pulse_decl decl))))
                 uu___1) (env, expected_t)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse_after_desugar"
    (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Syntax_Embeddings.debug_wrap
               "Pulse.Main.check_pulse_after_desugar"
               (fun _ ->
                  match args with
                  | (tv_0, _)::args_tail ->
                      (FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
                         "Pulse.Main.check_pulse_after_desugar (plugin)"
                         (FStar_Tactics_Native.from_tactic_2
                            check_pulse_after_desugar)
                         (FStar_Syntax_Embeddings.mk_any_emb tv_0)
                         (FStar_Syntax_Embeddings.e_tuple2
                            FStar_Reflection_V2_Embeddings.e_env
                            (FStar_Syntax_Embeddings.e_option
                               FStar_Reflection_V2_Embeddings.e_term))
                         (FStar_Syntax_Embeddings.e_tuple3
                            (FStar_Syntax_Embeddings.e_list
                               (FStar_Syntax_Embeddings.e_tuple3
                                  FStar_Syntax_Embeddings.e_bool
                                  FStar_Reflection_V2_Embeddings.e_sigelt
                                  (FStar_Syntax_Embeddings.e_option
                                     (FStar_Syntax_Embeddings.e_tuple2
                                        FStar_Syntax_Embeddings.e_string
                                        FStar_Reflection_V2_Embeddings.e_term))))
                            (FStar_Syntax_Embeddings.e_tuple3
                               FStar_Syntax_Embeddings.e_bool
                               FStar_Reflection_V2_Embeddings.e_sigelt
                               (FStar_Syntax_Embeddings.e_option
                                  (FStar_Syntax_Embeddings.e_tuple2
                                     FStar_Syntax_Embeddings.e_string
                                     FStar_Reflection_V2_Embeddings.e_term)))
                            (FStar_Syntax_Embeddings.e_list
                               (FStar_Syntax_Embeddings.e_tuple3
                                  FStar_Syntax_Embeddings.e_bool
                                  FStar_Reflection_V2_Embeddings.e_sigelt
                                  (FStar_Syntax_Embeddings.e_option
                                     (FStar_Syntax_Embeddings.e_tuple2
                                        FStar_Syntax_Embeddings.e_string
                                        FStar_Reflection_V2_Embeddings.e_term)))))
                         psc ncb us) args_tail
                  | _ -> failwith "arity mismatch"))