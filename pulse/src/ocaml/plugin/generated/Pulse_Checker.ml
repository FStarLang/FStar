open Prims
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (38))
               (Prims.of_int (23)) (Prims.of_int (38)) (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (38))
               (Prims.of_int (4)) (Prims.of_int (38)) (Prims.of_int (68)))))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (has_pure_vprops : Pulse_Syntax_Base.term -> Prims.bool) =
  fun pre ->
    FStar_List_Tot_Base.existsb
      (fun t -> Pulse_Syntax_Base.uu___is_Tm_Pure t.Pulse_Syntax_Base.t)
      (Pulse_Typing_Combinators.vprop_as_list pre)
let (elim_pure_explicit_lid : Prims.string Prims.list) =
  Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit"
let (default_binder_annot : Pulse_Syntax_Base.binder) =
  {
    Pulse_Syntax_Base.binder_ty = Pulse_Syntax_Base.tm_unknown;
    Pulse_Syntax_Base.binder_ppname = Pulse_Syntax_Base.ppname_default
  }
let rec (gen_names_for_unknowns :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        (((Pulse_Syntax_Base.nvar * Pulse_Syntax_Base.term) Prims.list *
           Pulse_Syntax_Base.term * Pulse_Syntax_Base.term Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun t ->
             fun ws ->
               match ws with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> ([], t, []))))
               | w::ws1 ->
                   Obj.magic
                     (Obj.repr
                        (match t.Pulse_Syntax_Base.t with
                         | Pulse_Syntax_Base.Tm_ExistsSL (uu___, b, body) ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (322))
                                        (Prims.of_int (10))
                                        (Prims.of_int (328))
                                        (Prims.of_int (27)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (320))
                                        (Prims.of_int (31))
                                        (Prims.of_int (336))
                                        (Prims.of_int (39)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match w.Pulse_Syntax_Base.t with
                                     | Pulse_Syntax_Base.Tm_Unknown ->
                                         ((FStar_Pervasives_Native.Some
                                             (Pulse_Typing_Env.fresh g)),
                                           (Pulse_Syntax_Pure.tm_var
                                              {
                                                Pulse_Syntax_Base.nm_index =
                                                  (Pulse_Typing_Env.fresh g);
                                                Pulse_Syntax_Base.nm_ppname =
                                                  (b.Pulse_Syntax_Base.binder_ppname)
                                              }),
                                           (Pulse_Typing_Env.push_binding g
                                              (Pulse_Typing_Env.fresh g)
                                              b.Pulse_Syntax_Base.binder_ppname
                                              b.Pulse_Syntax_Base.binder_ty))
                                     | uu___2 ->
                                         (FStar_Pervasives_Native.None, w, g)))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (xopt, w1, g1) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (329))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (329))
                                                       (Prims.of_int (42)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (329))
                                                       (Prims.of_int (45))
                                                       (Prims.of_int (336))
                                                       (Prims.of_int (39)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Pulse_Syntax_Naming.open_term'
                                                      body w1 Prims.int_zero))
                                              (fun uu___2 ->
                                                 (fun t1 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (330))
                                                                  (Prims.of_int (31))
                                                                  (Prims.of_int (330))
                                                                  (Prims.of_int (60)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (329))
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (336))
                                                                  (Prims.of_int (39)))))
                                                         (Obj.magic
                                                            (gen_names_for_unknowns
                                                               g1 t1 ws1))
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 match uu___2
                                                                 with
                                                                 | (new_names,
                                                                    t2, ws2)
                                                                    ->
                                                                    (match xopt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    x ->
                                                                    (((((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x),
                                                                    (b.Pulse_Syntax_Base.binder_ty))
                                                                    ::
                                                                    new_names),
                                                                    t2, (w1
                                                                    :: ws2))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (new_names,
                                                                    t2, (w1
                                                                    :: ws2)))))))
                                                   uu___2))) uu___1)
                         | uu___ ->
                             Pulse_Typing_Env.fail g
                               (FStar_Pervasives_Native.Some
                                  (t.Pulse_Syntax_Base.range1))
                               "intro exists with non-existential"))) uu___2
          uu___1 uu___
let (instantiate_unknown_witnesses :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (342))
                 (Prims.of_int (65)) (Prims.of_int (342)) (Prims.of_int (71)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (340))
                 (Prims.of_int (28)) (Prims.of_int (364)) (Prims.of_int (10)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> t.Pulse_Syntax_Base.term1))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | Pulse_Syntax_Base.Tm_IntroExists
                  { Pulse_Syntax_Base.erased = erased;
                    Pulse_Syntax_Base.p2 = p;
                    Pulse_Syntax_Base.witnesses = ws;
                    Pulse_Syntax_Base.should_check1 = should_check;_}
                  ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (344)) (Prims.of_int (36))
                                (Prims.of_int (344)) (Prims.of_int (65)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (342)) (Prims.of_int (74))
                                (Prims.of_int (364)) (Prims.of_int (10)))))
                       (Obj.magic (gen_names_for_unknowns g p ws))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match uu___1 with
                               | (new_names, opened_p, new_ws) ->
                                   (match new_names with
                                    | [] -> FStar_Pervasives_Native.None
                                    | uu___3 ->
                                        FStar_Pervasives_Native.Some
                                          (FStar_List_Tot_Base.fold_right
                                             (fun new_name ->
                                                fun e ->
                                                  match new_name with
                                                  | ((ppname, x), ty) ->
                                                      (match (Pulse_Syntax_Naming.close_st_term'
                                                                e x
                                                                Prims.int_zero).Pulse_Syntax_Base.term1
                                                       with
                                                       | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                           {
                                                             Pulse_Syntax_Base.hint_type
                                                               = hint_type;
                                                             Pulse_Syntax_Base.binders
                                                               = binders;
                                                             Pulse_Syntax_Base.v
                                                               = v;
                                                             Pulse_Syntax_Base.t4
                                                               = t1;_}
                                                           ->
                                                           {
                                                             Pulse_Syntax_Base.term1
                                                               =
                                                               (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                  {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    hint_type;
                                                                    Pulse_Syntax_Base.binders
                                                                    =
                                                                    ({
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = ty;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    } ::
                                                                    binders);
                                                                    Pulse_Syntax_Base.v
                                                                    = v;
                                                                    Pulse_Syntax_Base.t4
                                                                    = t1
                                                                  });
                                                             Pulse_Syntax_Base.range2
                                                               =
                                                               ((Pulse_Syntax_Naming.close_st_term'
                                                                   e x
                                                                   Prims.int_zero).Pulse_Syntax_Base.range2)
                                                           })) new_names
                                             {
                                               Pulse_Syntax_Base.term1 =
                                                 (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                    {
                                                      Pulse_Syntax_Base.hint_type
                                                        =
                                                        Pulse_Syntax_Base.ASSERT;
                                                      Pulse_Syntax_Base.binders
                                                        = [];
                                                      Pulse_Syntax_Base.v =
                                                        opened_p;
                                                      Pulse_Syntax_Base.t4 =
                                                        {
                                                          Pulse_Syntax_Base.term1
                                                            =
                                                            (Pulse_Syntax_Base.Tm_IntroExists
                                                               {
                                                                 Pulse_Syntax_Base.erased
                                                                   = erased;
                                                                 Pulse_Syntax_Base.p2
                                                                   = p;
                                                                 Pulse_Syntax_Base.witnesses
                                                                   = new_ws;
                                                                 Pulse_Syntax_Base.should_check1
                                                                   =
                                                                   should_check
                                                               });
                                                          Pulse_Syntax_Base.range2
                                                            =
                                                            (t.Pulse_Syntax_Base.range2)
                                                        }
                                                    });
                                               Pulse_Syntax_Base.range2 =
                                                 (t.Pulse_Syntax_Base.range2)
                                             })))))) uu___)
let rec (transform_to_unary_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun ws ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (369)) (Prims.of_int (21))
                   (Prims.of_int (369)) (Prims.of_int (39)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (370)) (Prims.of_int (2))
                   (Prims.of_int (384)) (Prims.of_int (68)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Syntax_Base.should_check_false))
          (fun uu___ ->
             (fun should_check ->
                match ws with
                | [] ->
                    Obj.magic
                      (Obj.repr
                         (Pulse_Typing_Env.fail g
                            (FStar_Pervasives_Native.Some
                               (t.Pulse_Syntax_Base.range1))
                            "intro exists with empty witnesses"))
                | w::[] ->
                    Obj.magic
                      (Obj.repr
                         (if
                            Pulse_Syntax_Base.uu___is_Tm_ExistsSL
                              t.Pulse_Syntax_Base.t
                          then
                            Obj.repr
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_Typing.wr
                                      (Pulse_Syntax_Base.Tm_IntroExists
                                         {
                                           Pulse_Syntax_Base.erased = false;
                                           Pulse_Syntax_Base.p2 = t;
                                           Pulse_Syntax_Base.witnesses = [w];
                                           Pulse_Syntax_Base.should_check1 =
                                             should_check
                                         })))
                          else
                            Obj.repr
                              (Pulse_Typing_Env.fail g
                                 (FStar_Pervasives_Native.Some
                                    (t.Pulse_Syntax_Base.range1))
                                 "intro exists with non-existential")))
                | w::ws1 ->
                    Obj.magic
                      (Obj.repr
                         (match t.Pulse_Syntax_Base.t with
                          | Pulse_Syntax_Base.Tm_ExistsSL (u, b, body) ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (379))
                                         (Prims.of_int (17))
                                         (Prims.of_int (379))
                                         (Prims.of_int (43)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (379))
                                         (Prims.of_int (46))
                                         (Prims.of_int (383))
                                         (Prims.of_int (91)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      Pulse_Syntax_Naming.subst_term body
                                        [Pulse_Syntax_Naming.DT
                                           (Prims.int_zero, w)]))
                                (fun uu___ ->
                                   (fun body1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (380))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (380))
                                                    (Prims.of_int (56)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (381))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (383))
                                                    (Prims.of_int (91)))))
                                           (Obj.magic
                                              (transform_to_unary_intro_exists
                                                 g body1 ws1))
                                           (fun st ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   Pulse_Typing.wr
                                                     (Pulse_Syntax_Base.Tm_Bind
                                                        {
                                                          Pulse_Syntax_Base.binder
                                                            =
                                                            (Pulse_Syntax_Base.null_binder
                                                               Pulse_Typing.tm_unit);
                                                          Pulse_Syntax_Base.head1
                                                            = st;
                                                          Pulse_Syntax_Base.body1
                                                            =
                                                            (Pulse_Typing.wr
                                                               (Pulse_Syntax_Base.Tm_IntroExists
                                                                  {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p2
                                                                    = t;
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [w];
                                                                    Pulse_Syntax_Base.should_check1
                                                                    =
                                                                    should_check
                                                                  }))
                                                        }))))) uu___)
                          | uu___ ->
                              Pulse_Typing_Env.fail g
                                (FStar_Pervasives_Native.Some
                                   (t.Pulse_Syntax_Base.range1))
                                "intro exists with non-existential"))) uu___)
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun g0 ->
      fun pre0 ->
        fun pre0_typing ->
          fun post_hint ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (415)) (Prims.of_int (4))
                         (Prims.of_int (415)) (Prims.of_int (47)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (393)) (Prims.of_int (20))
                         (Prims.of_int (506)) (Prims.of_int (50)))))
                (Obj.magic (Pulse_Prover_ElimPure.elim_pure g0 pre0 ()))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Pervasives.Mkdtuple4
                          (g, pre, pre_typing, k_elim_pure) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (417))
                                        (Prims.of_int (44))
                                        (Prims.of_int (502))
                                        (Prims.of_int (48)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (503))
                                        (Prims.of_int (4))
                                        (Prims.of_int (506))
                                        (Prims.of_int (50)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (418))
                                              (Prims.of_int (12))
                                              (Prims.of_int (418))
                                              (Prims.of_int (55)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (420))
                                              (Prims.of_int (4))
                                              (Prims.of_int (502))
                                              (Prims.of_int (48)))))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           Pulse_Checker_Pure.push_context
                                             (Pulse_Syntax_Printer.tag_of_st_term
                                                t) t.Pulse_Syntax_Base.range2
                                             g))
                                     (fun uu___1 ->
                                        (fun g1 ->
                                           match t.Pulse_Syntax_Base.term1
                                           with
                                           | Pulse_Syntax_Base.Tm_Protect
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_V2_Derived.fail
                                                       "Protect should have been removed"))
                                           | Pulse_Syntax_Base.Tm_Return
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_Return.check_return
                                                       g1 t pre () post_hint))
                                           | Pulse_Syntax_Base.Tm_Abs uu___1
                                               ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_V2_Derived.fail
                                                       "Tm_Abs check should not have been called in the checker"))
                                           | Pulse_Syntax_Base.Tm_STApp
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_STApp.check_stapp
                                                       g1 t pre () post_hint))
                                           | Pulse_Syntax_Base.Tm_ElimExists
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_Exists.check_elim_exists
                                                       g1 t pre () post_hint))
                                           | Pulse_Syntax_Base.Tm_IntroExists
                                               {
                                                 Pulse_Syntax_Base.erased =
                                                   uu___1;
                                                 Pulse_Syntax_Base.p2 = p;
                                                 Pulse_Syntax_Base.witnesses
                                                   = witnesses;
                                                 Pulse_Syntax_Base.should_check1
                                                   = uu___2;_}
                                               ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (435))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (435))
                                                                (Prims.of_int (46)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (435))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (446))
                                                                (Prims.of_int (52)))))
                                                       (Obj.magic
                                                          (instantiate_unknown_witnesses
                                                             g1 t))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             match uu___3
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 t1 ->
                                                                 Obj.magic
                                                                   (check'
                                                                    true g1
                                                                    pre ()
                                                                    post_hint
                                                                    t1)
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 (match witnesses
                                                                  with
                                                                  | [] ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    "intro exists with empty witnesses")
                                                                  | uu___4::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Exists.check_intro_exists_either
                                                                    g1 t
                                                                    FStar_Pervasives_Native.None
                                                                    pre ()
                                                                    post_hint)
                                                                  | uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (transform_to_unary_intro_exists
                                                                    g1 p
                                                                    witnesses))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    true g1
                                                                    pre ()
                                                                    post_hint
                                                                    t1))
                                                                    uu___5))))
                                                            uu___3)))
                                           | Pulse_Syntax_Base.Tm_Bind uu___1
                                               ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_Bind.check_bind
                                                       g1 t pre () post_hint
                                                       (check' true)))
                                           | Pulse_Syntax_Base.Tm_TotBind
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_Bind.check_tot_bind
                                                       g1 t pre () post_hint
                                                       (check' true)))
                                           | Pulse_Syntax_Base.Tm_If
                                               { Pulse_Syntax_Base.b1 = b;
                                                 Pulse_Syntax_Base.then_ = e1;
                                                 Pulse_Syntax_Base.else_ = e2;
                                                 Pulse_Syntax_Base.post1 =
                                                   post_if;_}
                                               ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (474))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (490))
                                                                (Prims.of_int (97)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (491))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (494))
                                                                (Prims.of_int (29)))))
                                                       (match (post_if,
                                                                post_hint)
                                                        with
                                                        | (FStar_Pervasives_Native.None,
                                                           FStar_Pervasives_Native.Some
                                                           p) ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    p)))
                                                        | (FStar_Pervasives_Native.Some
                                                           p,
                                                           FStar_Pervasives_Native.None)
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    p))
                                                        | (FStar_Pervasives_Native.Some
                                                           p,
                                                           FStar_Pervasives_Native.Some
                                                           q) ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    p))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (58)))))
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
                                                                    q.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Multiple annotated postconditions---remove one of them.\nThe context expects the postcondition "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    ",\nbut this conditional was annotated with postcondition "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1)))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___1))
                                                                    uu___1)))
                                                        | (uu___1, uu___2) ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\nEither annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")))
                                                       (fun uu___1 ->
                                                          (fun post ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (63)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (29)))))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_If.check_if
                                                                    g1 b e1
                                                                    e2 pre ()
                                                                    post
                                                                    (check'
                                                                    true)))
                                                                  (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, t1,
                                                                    pre',
                                                                    g11, k)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, t1,
                                                                    pre',
                                                                    g11, k)))))
                                                            uu___1)))
                                           | Pulse_Syntax_Base.Tm_While
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_While.check_while
                                                       g1 t pre () post_hint
                                                       (check' true)))
                                           | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                               uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_AssertWithBinders.check
                                                       g1 t pre () post_hint
                                                       (check' true)))
                                           | uu___1 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_V2_Derived.fail
                                                       "Checker form not implemented")))
                                          uu___1)))
                               (fun r ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       match r with
                                       | FStar_Pervasives.Mkdtuple5
                                           (x, t1, pre', g1, k) ->
                                           FStar_Pervasives.Mkdtuple5
                                             (x, t1, pre', g1,
                                               (Pulse_Checker_Common.k_elab_trans
                                                  g0 g g1 pre0 pre pre'
                                                  k_elim_pure k)))))) uu___)
let (check : Pulse_Checker_Common.check_t) = check' true