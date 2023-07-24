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
            Pulse_Typing.ST_VPropEquiv (g, c, c', x, (), (), (), (), ()) in
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
                     (Prims.of_int (46)) (Prims.of_int (13))
                     (Prims.of_int (46)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                     (Prims.of_int (47)) (Prims.of_int (2))
                     (Prims.of_int (61)) (Prims.of_int (82)))))
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
                                    (Prims.of_int (49)) (Prims.of_int (12))
                                    (Prims.of_int (49)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.STApp.fst"
                                    (Prims.of_int (49)) (Prims.of_int (37))
                                    (Prims.of_int (60)) (Prims.of_int (7)))))
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
                                               (Prims.of_int (50))
                                               (Prims.of_int (15))
                                               (Prims.of_int (50))
                                               (Prims.of_int (60)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.STApp.fst"
                                               (Prims.of_int (52))
                                               (Prims.of_int (6))
                                               (Prims.of_int (59))
                                               (Prims.of_int (96)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            Pulse_Typing_Env.push_binding uvs
                                              x
                                              Pulse_Syntax_Base.ppname_default
                                              b.Pulse_Syntax_Base.binder_ty))
                                      (fun uu___ ->
                                         (fun uvs' ->
                                            match c_rest with
                                            | Pulse_Syntax_Base.C_ST uu___ ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
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
                                                                    =
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)
                                                                    });
                                                                 Pulse_Syntax_Base.range2
                                                                   =
                                                                   (t.Pulse_Syntax_Base.range1)
                                                               }))))
                                            | Pulse_Syntax_Base.C_STAtomic
                                                (uu___, uu___1) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
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
                                                                    =
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)
                                                                    });
                                                                 Pulse_Syntax_Base.range2
                                                                   =
                                                                   (t.Pulse_Syntax_Base.range1)
                                                               }))))
                                            | Pulse_Syntax_Base.C_STGhost
                                                (uu___, uu___1) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
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
                                                                    =
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)
                                                                    });
                                                                 Pulse_Syntax_Base.range2
                                                                   =
                                                                   (t.Pulse_Syntax_Base.range1)
                                                               }))))
                                            | Pulse_Syntax_Base.C_Tot ty1 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (intro_uvars_for_logical_implicits
                                                        g uvs'
                                                        (Pulse_Syntax_Pure.tm_pureapp
                                                           t
                                                           (FStar_Pervasives_Native.Some
                                                              Pulse_Syntax_Base.Implicit)
                                                           (Pulse_Syntax_Pure.null_var
                                                              x)) ty1)))
                                           uu___))) uu___))
                  | uu___ ->
                      Obj.magic
                        (Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                           "intro_uvars_for_logical_implicits in stapp, unexpected type"))
                 uu___)
let (instantaite_implicits :
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
                 (Prims.of_int (68)) (Prims.of_int (14)) (Prims.of_int (68))
                 (Prims.of_int (21)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                 (Prims.of_int (68)) (Prims.of_int (24)) (Prims.of_int (81))
                 (Prims.of_int (72)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> t.Pulse_Syntax_Base.range2))
        (fun uu___ ->
           (fun range ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                            (Prims.of_int (69)) (Prims.of_int (46))
                            (Prims.of_int (69)) (Prims.of_int (52)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                            (Prims.of_int (68)) (Prims.of_int (24))
                            (Prims.of_int (81)) (Prims.of_int (72)))))
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
                                           (Prims.of_int (70))
                                           (Prims.of_int (17))
                                           (Prims.of_int (70))
                                           (Prims.of_int (41)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.STApp.fst"
                                           (Prims.of_int (70))
                                           (Prims.of_int (44))
                                           (Prims.of_int (81))
                                           (Prims.of_int (72)))))
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
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (51)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.STApp.fst"
                                                      (Prims.of_int (70))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (81))
                                                      (Prims.of_int (72)))))
                                             (Obj.magic
                                                (Pulse_Checker_Pure.instantiate_term_implicits
                                                   g pure_app))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | (t1, ty) ->
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
                                                                    g
                                                                    (
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)) t1 ty))
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
                                                                    ((Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)),
                                                                    (Pulse_Typing_Env.push_env
                                                                    g
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g))),
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
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (t1.Pulse_Syntax_Base.range1)
                                                                    })))
                                                                  | uu___3 ->
                                                                    Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "instantiate_implicits in stapp, unexpected term")))))
                                                  uu___1))) uu___1))) uu___)))
             uu___)
let (check_stapp :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g0 ->
    fun t ->
      fun ctxt ->
        fun ctxt_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                       (Prims.of_int (92)) (Prims.of_int (11))
                       (Prims.of_int (92)) (Prims.of_int (43)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                       (Prims.of_int (92)) (Prims.of_int (46))
                       (Prims.of_int (137)) (Prims.of_int (123)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Checker_Pure.push_context "st_app"
                      t.Pulse_Syntax_Base.range2 g0))
              (fun uu___ ->
                 (fun g01 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.STApp.fst"
                                  (Prims.of_int (93)) (Prims.of_int (14))
                                  (Prims.of_int (93)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.STApp.fst"
                                  (Prims.of_int (93)) (Prims.of_int (24))
                                  (Prims.of_int (137)) (Prims.of_int (123)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> t.Pulse_Syntax_Base.range2))
                         (fun uu___ ->
                            (fun range ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.STApp.fst"
                                             (Prims.of_int (95))
                                             (Prims.of_int (24))
                                             (Prims.of_int (95))
                                             (Prims.of_int (50)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.STApp.fst"
                                             (Prims.of_int (93))
                                             (Prims.of_int (24))
                                             (Prims.of_int (137))
                                             (Prims.of_int (123)))))
                                    (Obj.magic (instantaite_implicits g01 t))
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
                                                            (Prims.of_int (97))
                                                            (Prims.of_int (46))
                                                            (Prims.of_int (97))
                                                            (Prims.of_int (52)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.STApp.fst"
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (53))
                                                            (Prims.of_int (137))
                                                            (Prims.of_int (123)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         t1.Pulse_Syntax_Base.term1))
                                                   (fun uu___1 ->
                                                      (fun uu___1 ->
                                                         match uu___1 with
                                                         | Pulse_Syntax_Base.Tm_STApp
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
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (52)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (123)))))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g head))
                                                                  (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (head1,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (123)))))
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
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (102))
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
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
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
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "st_app: head = "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", ty_head = "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
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
                                                                    ({
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = formal;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;_},
                                                                    bqual,
                                                                    comp_typ)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (44)))))
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
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "st_app, readback comp as "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___5))
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if
                                                                    qual =
                                                                    bqual
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (126)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g arg
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
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    canonicalize_st_typing
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
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    d1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre_uvs
                                                                    g0 ctxt
                                                                    () uvs t2
                                                                    c d2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.repack
                                                                    g0 ctxt
                                                                    uu___6
                                                                    post_hint
                                                                    t2.Pulse_Syntax_Base.range2))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___6,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    canonicalize_st_typing
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
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    d1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre_uvs
                                                                    g0 ctxt
                                                                    () uvs t2
                                                                    c d2))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.repack
                                                                    g0 ctxt
                                                                    uu___7
                                                                    post_hint
                                                                    t2.Pulse_Syntax_Base.range2))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___6,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    canonicalize_st_typing
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
                                                                    }))
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    canon_comp
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    d1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre_uvs
                                                                    g0 ctxt
                                                                    () uvs t2
                                                                    c d2))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.repack
                                                                    g0 ctxt
                                                                    uu___7
                                                                    post_hint
                                                                    t2.Pulse_Syntax_Base.range2))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t1.Pulse_Syntax_Base.range2))
                                                                    "Expected an effectful application; got a pure term (could it be partially applied by mistake?)")))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
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
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
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
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unexpected qualifier in head type "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    " of stateful application: head = "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", arg = "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
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
                                                                    (t1.Pulse_Syntax_Base.range2))
                                                                    uu___6))
                                                                    uu___6)))
                                                                    uu___4))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (123)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (122)))))
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
                                                                    ty_head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Unexpected head type in impure application: "
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
                                                                    (t1.Pulse_Syntax_Base.range2))
                                                                    uu___5))
                                                                    uu___5)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                        uu___1))) uu___)))
                              uu___))) uu___)