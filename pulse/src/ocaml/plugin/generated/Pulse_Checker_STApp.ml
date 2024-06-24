open Prims
let (debug_log :
  Pulse_Typing_Env.env ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "st_app"
           then Obj.magic (Obj.repr (f ()))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (canon_comp : Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st) =
  fun c ->
    match Pulse_Readback.readback_comp (Pulse_Elaborate_Pure.elab_comp c)
    with
    | FStar_Pervasives_Native.None -> c
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.C_Tot uu___) -> c
    | FStar_Pervasives_Native.Some c' -> c'
let (canon_comp_eq_res :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      FStar_Reflection_Typing.Rel_refl
        ((Pulse_Typing.elab_env g), (Pulse_Syntax_Base.comp_res c),
          FStar_Reflection_Typing.R_Eq)
let (canonicalize_st_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          let c' = canon_comp c in
          let x = Pulse_Typing_Env.fresh g in
          let st_eq =
            Pulse_Typing.ST_VPropEquiv
              (g, c, c', x, (), (), (), (canon_comp_eq_res g c), (), ()) in
          Pulse_Typing.T_Equiv (g, t, c, c', d, st_eq)
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let rec (intro_uvars_for_logical_implicits :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Typing_Env.env, Pulse_Typing_Env.env,
             Pulse_Syntax_Base.st_term) FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun ty ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                     (Prims.of_int (66)) (Prims.of_int (13))
                     (Prims.of_int (66)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                     (Prims.of_int (67)) (Prims.of_int (2))
                     (Prims.of_int (90)) (Prims.of_int (31)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Syntax_Pure.is_arrow ty))
            (fun uu___ ->
               (fun ropt ->
                  match ropt with
                  | FStar_Pervasives_Native.Some
                      (b, FStar_Pervasives_Native.Some
                       (Pulse_Syntax_Base.Implicit), c_rest)
                      ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (69)) (Prims.of_int (12))
                                    (Prims.of_int (69)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (69)) (Prims.of_int (37))
                                    (Prims.of_int (85)) (Prims.of_int (7)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 Pulse_Typing_Env.fresh
                                   (Pulse_Typing_Env.push_env g uvs)))
                           (fun uu___ ->
                              (fun x ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (70))
                                               (Prims.of_int (17))
                                               (Prims.of_int (70))
                                               (Prims.of_int (48)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (70))
                                               (Prims.of_int (51))
                                               (Prims.of_int (85))
                                               (Prims.of_int (7)))))
                                      (Obj.magic
                                         (Pulse_Syntax_Base.ppname_for_uvar
                                            b.Pulse_Syntax_Base.binder_ppname))
                                      (fun uu___ ->
                                         (fun ppname ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.STApp.fst"
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (52)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.STApp.fst"
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (85))
                                                          (Prims.of_int (7)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ ->
                                                       Pulse_Typing_Env.push_binding
                                                         uvs x ppname
                                                         b.Pulse_Syntax_Base.binder_ty))
                                                 (fun uu___ ->
                                                    (fun uvs' ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (47)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (7)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___ ->
                                                                  {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                  }))
                                                            (fun uu___ ->
                                                               (fun var ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    var))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    t_var ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.open_comp_with
                                                                    c_rest
                                                                    t_var))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    c_rest1
                                                                    ->
                                                                    match c_rest1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs',
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs'),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = t;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit);
                                                                    Pulse_Syntax_Base.arg
                                                                    = t_var
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_rest1))
                                                                    }))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___,
                                                                    uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs',
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs'),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = t;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit);
                                                                    Pulse_Syntax_Base.arg
                                                                    = t_var
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_rest1))
                                                                    }))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___,
                                                                    uu___1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs',
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs'),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = t;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit);
                                                                    Pulse_Syntax_Base.arg
                                                                    = t_var
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_rest1))
                                                                    }))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    ty1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (intro_uvars_for_logical_implicits
                                                                    g uvs'
                                                                    (Pulse_Syntax_Pure.tm_pureapp
                                                                    t
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit)
                                                                    t_var)
                                                                    ty1)))
                                                                    uu___)))
                                                                    uu___)))
                                                                 uu___)))
                                                      uu___))) uu___))) uu___))
                  | uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (88)) (Prims.of_int (6))
                                    (Prims.of_int (90)) (Prims.of_int (31)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (87)) (Prims.of_int (4))
                                    (Prims.of_int (90)) (Prims.of_int (31)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.STApp.fst"
                                          (Prims.of_int (90))
                                          (Prims.of_int (9))
                                          (Prims.of_int (90))
                                          (Prims.of_int (30)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (590))
                                          (Prims.of_int (19))
                                          (Prims.of_int (590))
                                          (Prims.of_int (31)))))
                                 (Obj.magic
                                    (Pulse_Syntax_Printer.term_to_string ty))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         Prims.strcat
                                           "check_stapp.intro_uvars_for_logical_implicits: expected an arrow type,with an implicit parameter, found: "
                                           (Prims.strcat uu___1 "")))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (Pulse_Typing_Env.fail g
                                      FStar_Pervasives_Native.None uu___1))
                                uu___1))) uu___)
let (instantiate_implicits :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Typing_Env.env, Pulse_Typing_Env.env,
         Pulse_Syntax_Base.st_term) FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                 (Prims.of_int (97)) (Prims.of_int (14)) (Prims.of_int (97))
                 (Prims.of_int (21)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                 (Prims.of_int (97)) (Prims.of_int (24)) (Prims.of_int (112))
                 (Prims.of_int (20)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> t.Pulse_Syntax_Base.range1))
        (fun uu___ ->
           (fun range ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                            (Prims.of_int (98)) (Prims.of_int (46))
                            (Prims.of_int (98)) (Prims.of_int (52)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                            (Prims.of_int (97)) (Prims.of_int (24))
                            (Prims.of_int (112)) (Prims.of_int (20)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> t.Pulse_Syntax_Base.term1))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | Pulse_Syntax_Base.Tm_STApp
                             { Pulse_Syntax_Base.head = head;
                               Pulse_Syntax_Base.arg_qual = qual;
                               Pulse_Syntax_Base.arg = arg;_}
                             ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (17))
                                           (Prims.of_int (99))
                                           (Prims.of_int (41)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (44))
                                           (Prims.of_int (112))
                                           (Prims.of_int (20)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Pulse_Syntax_Pure.tm_pureapp head
                                          qual arg))
                                  (fun uu___1 ->
                                     (fun pure_app ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.STApp.fst"
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (66)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.STApp.fst"
                                                      (Prims.of_int (99))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (112))
                                                      (Prims.of_int (20)))))
                                             (Obj.magic
                                                (Pulse_Checker_Pure.instantiate_term_implicits_uvs
                                                   g pure_app))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | FStar_Pervasives.Mkdtuple3
                                                       (uvs, t1, ty) ->
                                                       (match Pulse_Syntax_Pure.is_arrow
                                                                ty
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            (uu___2,
                                                             FStar_Pervasives_Native.Some
                                                             (Pulse_Syntax_Base.Implicit),
                                                             uu___3)
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (intro_uvars_for_logical_implicits
                                                                    g uvs t1
                                                                    ty))
                                                        | uu___2 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (match 
                                                                    Pulse_Syntax_Pure.is_pure_app
                                                                    t1
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    (head1,
                                                                    q, arg1)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs,
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = q;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    Pulse_Syntax_Base.default_effect_hint
                                                                    })))
                                                                  | uu___3 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    t1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "check_stapp.instantiate_implicits: expected an application term, found: "
                                                                    (Prims.strcat
                                                                    uu___4 "")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t1))
                                                                    uu___4))
                                                                    uu___4))))))
                                                  uu___1))) uu___1))) uu___)))
             uu___)
let (should_allow_ambiguous :
  Pulse_Syntax_Base.term -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
               (Prims.of_int (117)) (Prims.of_int (18)) (Prims.of_int (117))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
               (Prims.of_int (118)) (Prims.of_int (2)) (Prims.of_int (125))
               (Prims.of_int (57)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> "Pulse.Lib.Core.allow_ambiguous"))
      (fun uu___ ->
         (fun attr_name ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                          (Prims.of_int (118)) (Prims.of_int (8))
                          (Prims.of_int (118)) (Prims.of_int (15)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                          (Prims.of_int (118)) (Prims.of_int (2))
                          (Prims.of_int (125)) (Prims.of_int (57)))))
                 (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.hua t))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> false)))
                       | FStar_Pervasives_Native.Some (hfv, uu___1, uu___2)
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.STApp.fst"
                                            (Prims.of_int (121))
                                            (Prims.of_int (10))
                                            (Prims.of_int (121))
                                            (Prims.of_int (56)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.STApp.fst"
                                            (Prims.of_int (121))
                                            (Prims.of_int (4))
                                            (Prims.of_int (125))
                                            (Prims.of_int (57)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.STApp.fst"
                                                  (Prims.of_int (121))
                                                  (Prims.of_int (23))
                                                  (Prims.of_int (121))
                                                  (Prims.of_int (37)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.STApp.fst"
                                                  (Prims.of_int (121))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (121))
                                                  (Prims.of_int (56)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.top_env
                                               ()))
                                         (fun uu___3 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 ->
                                                 FStar_Reflection_V2_Builtins.lookup_typ
                                                   uu___3
                                                   (FStar_Reflection_V2_Builtins.inspect_fv
                                                      hfv)))))
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         match uu___3 with
                                         | FStar_Pervasives_Native.None ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 -> false)))
                                         | FStar_Pervasives_Native.Some se ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.STApp.fst"
                                                              (Prims.of_int (124))
                                                              (Prims.of_int (18))
                                                              (Prims.of_int (124))
                                                              (Prims.of_int (35)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.STApp.fst"
                                                              (Prims.of_int (125))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (125))
                                                              (Prims.of_int (57)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           FStar_Reflection_V2_Builtins.sigelt_attrs
                                                             se))
                                                     (fun uu___4 ->
                                                        (fun attrs ->
                                                           Obj.magic
                                                             (FStar_Tactics_Util.tryFind
                                                                (fun uu___4
                                                                   ->
                                                                   (fun a ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_V2_Derived.is_fvar
                                                                    a
                                                                    attr_name)))
                                                                    uu___4)
                                                                attrs))
                                                          uu___4)))) uu___3))))
                      uu___))) uu___)
let (apply_impure_function :
  Pulse_Syntax_Base.range ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              unit Pulse_Typing.post_hint_opt ->
                Pulse_Syntax_Base.ppname ->
                  Pulse_Syntax_Base.term ->
                    Pulse_Syntax_Base.qualifier
                      FStar_Pervasives_Native.option ->
                      Pulse_Syntax_Base.term ->
                        Pulse_Syntax_Base.term ->
                          FStar_TypeChecker_Core.tot_or_ghost ->
                            unit ->
                              (Pulse_Syntax_Base.binder *
                                Pulse_Syntax_Base.qualifier
                                FStar_Pervasives_Native.option *
                                Pulse_Syntax_Base.comp) ->
                                ((unit, unit, unit)
                                   Pulse_Checker_Base.checker_result_t,
                                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun range ->
    fun g0 ->
      fun uvs ->
        fun g ->
          fun ctxt ->
            fun ctxt_typing ->
              fun post_hint ->
                fun res_ppname ->
                  fun head ->
                    fun qual ->
                      fun arg ->
                        fun ty_head ->
                          fun eff_head ->
                            fun dhead ->
                              fun b ->
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (145))
                                           (Prims.of_int (67))
                                           (Prims.of_int (145))
                                           (Prims.of_int (68)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (145))
                                           (Prims.of_int (3))
                                           (Prims.of_int (225))
                                           (Prims.of_int (5)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> b))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | ({
                                             Pulse_Syntax_Base.binder_ty =
                                               formal;
                                             Pulse_Syntax_Base.binder_ppname
                                               = ppname;
                                             Pulse_Syntax_Base.binder_attrs =
                                               uu___1;_},
                                           bqual, comp_typ) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.STApp.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (38))
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (47)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.STApp.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (50))
                                                          (Prims.of_int (225))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 -> post_hint))
                                                 (fun uu___2 ->
                                                    (fun post_hint1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (53)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (5)))))
                                                            (Obj.magic
                                                               (should_allow_ambiguous
                                                                  head))
                                                            (fun uu___2 ->
                                                               (fun
                                                                  allow_ambiguous
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    comp_typ))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (152))
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
                                                                    "st_app, head="
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", arg="))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", readback comp as "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
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
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___3))
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    comp_typ))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    allow_ghost
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (5)))))
                                                                    (if
                                                                    (Prims.op_Negation
                                                                    allow_ghost)
                                                                    &&
                                                                    (eff_head
                                                                    =
                                                                    FStar_TypeChecker_Core.E_Ghost)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (37)))))
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
                                                                    head))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "head term "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " is ghost, but the arrow comp is not STGhost")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    uu___3))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    if
                                                                    qual <>
                                                                    bqual
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unexpected qualifier in head type "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    " of stateful application: head = "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", arg = "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5)))
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
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    uu___4))
                                                                    uu___4))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    if
                                                                    allow_ghost
                                                                    then
                                                                    FStar_TypeChecker_Core.E_Ghost
                                                                    else
                                                                    FStar_TypeChecker_Core.E_Total))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    eff_arg
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g arg
                                                                    eff_arg
                                                                    formal))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (arg1,
                                                                    darg) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ({
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    = range;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    comp_typ))
                                                                    },
                                                                    (canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)),
                                                                    (canonicalize_st_typing
                                                                    g
                                                                    (Pulse_Typing.wrst
                                                                    comp_typ
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)
                                                                    (Pulse_Typing.T_STApp
                                                                    (g, head,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___6,
                                                                    uu___7,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ({
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    = range;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    comp_typ))
                                                                    },
                                                                    (canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)),
                                                                    (canonicalize_st_typing
                                                                    g
                                                                    (Pulse_Typing.wrst
                                                                    comp_typ
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)
                                                                    (Pulse_Typing.T_STApp
                                                                    (g, head,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___6,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (23)))))
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
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (23)))))
                                                                    (if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars_comp
                                                                    comp_typ)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    "Unexpected clash of variable names, please file a bug-report"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.is_non_informative
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    formal)
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    token ->
                                                                    match token
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (103)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (102)))))
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
                                                                    comp_typ))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Unexpected non-informative result for "
                                                                    (Prims.strcat
                                                                    uu___8 "")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    uu___8))
                                                                    uu___8)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    token1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Reflection_Typing.Non_informative_token
                                                                    ((Pulse_Typing.elab_env
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    formal)),
                                                                    (Pulse_Elaborate_Pure.elab_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x))), ())))))
                                                                    uu___8)))
                                                                    (fun
                                                                    d_non_info
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ({
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    = range;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    },
                                                                    (canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)),
                                                                    (canonicalize_st_typing
                                                                    g
                                                                    (Pulse_Typing.wrst
                                                                    comp_typ
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)
                                                                    (Pulse_Typing.T_STGhostApp
                                                                    (g, head,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, x,
                                                                    (), (),
                                                                    ()))))))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    range)
                                                                    "Expected an effectful application; got a pure term (could it be partially applied by mistake?)")))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
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
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g t c d
                                                                    post_hint1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (st', c',
                                                                    st_typing')
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_bool
                                                                    allow_ambiguous))
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
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_comp
                                                                    c'))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "st_app: c' = "
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    "\n\tallow_ambiguous = "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    uu___10))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___10))
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (113)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre_uvs
                                                                    allow_ambiguous
                                                                    g0 ctxt
                                                                    () uvs
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (st', c',
                                                                    st_typing'))
                                                                    res_ppname))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    framed ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g0 ctxt
                                                                    framed
                                                                    post_hint1
                                                                    range))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                 uu___2)))
                                                      uu___2))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g0 ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                         (Prims.of_int (237)) (Prims.of_int (11))
                         (Prims.of_int (237)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                         (Prims.of_int (237)) (Prims.of_int (46))
                         (Prims.of_int (268)) (Prims.of_int (117)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "st_app"
                        t.Pulse_Syntax_Base.range1 g0))
                (fun uu___ ->
                   (fun g01 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (238)) (Prims.of_int (14))
                                    (Prims.of_int (238)) (Prims.of_int (21)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (238)) (Prims.of_int (24))
                                    (Prims.of_int (268)) (Prims.of_int (117)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> t.Pulse_Syntax_Base.range1))
                           (fun uu___ ->
                              (fun range ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (240))
                                               (Prims.of_int (24))
                                               (Prims.of_int (240))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (238))
                                               (Prims.of_int (24))
                                               (Prims.of_int (268))
                                               (Prims.of_int (117)))))
                                      (Obj.magic
                                         (instantiate_implicits g01 t))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            match uu___ with
                                            | FStar_Pervasives.Mkdtuple3
                                                (uvs, g, t1) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.STApp.fst"
                                                              (Prims.of_int (242))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (242))
                                                              (Prims.of_int (45)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.STApp.fst"
                                                              (Prims.of_int (242))
                                                              (Prims.of_int (48))
                                                              (Prims.of_int (268))
                                                              (Prims.of_int (117)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           post_hint))
                                                     (fun uu___1 ->
                                                        (fun post_hint1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (52)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (117)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    t1.Pulse_Syntax_Base.term1))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.compute_term_type
                                                                    g head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (head1,
                                                                    eff_head,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
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
                                                                    "st_app: head = "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", eff_head: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", ty_head = "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    (Pulse_Syntax_Printer.tot_or_ghost_to_string
                                                                    eff_head)))))
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
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___4))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty_head
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    b ->
                                                                    Obj.magic
                                                                    (apply_impure_function
                                                                    t1.Pulse_Syntax_Base.range1
                                                                    g01 uvs g
                                                                    ctxt ()
                                                                    post_hint1
                                                                    res_ppname
                                                                    head1
                                                                    qual arg
                                                                    ty_head
                                                                    eff_head
                                                                    () b)
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.norm_typing
                                                                    g head1
                                                                    eff_head
                                                                    ty_head
                                                                    ()
                                                                    [FStar_Pervasives.weak;
                                                                    FStar_Pervasives.hnf;
                                                                    FStar_Pervasives.delta]))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (ty',
                                                                    typing)
                                                                    ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Expected an arrow type; but head "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    " has type "))
                                                                    (Prims.strcat
                                                                    x "")))))
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
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t1.Pulse_Syntax_Base.range1))
                                                                    uu___6))
                                                                    uu___6))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    b ->
                                                                    Obj.magic
                                                                    (apply_impure_function
                                                                    t1.Pulse_Syntax_Base.range1
                                                                    g01 uvs g
                                                                    ctxt ()
                                                                    post_hint1
                                                                    res_ppname
                                                                    head1
                                                                    qual arg
                                                                    ty'
                                                                    eff_head
                                                                    () b)))
                                                                    uu___5)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                          uu___1))) uu___)))
                                uu___))) uu___)