open Prims
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (55))
               (Prims.of_int (23)) (Prims.of_int (55)) (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (55))
               (Prims.of_int (4)) (Prims.of_int (55)) (Prims.of_int (68)))))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (default_binder_annot : Pulse_Syntax_Base.binder) =
  Pulse_Syntax_Base.mk_binder_ppname Pulse_Syntax_Pure.tm_unknown
    Pulse_Syntax_Base.ppname_default
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
                        (match Pulse_Syntax_Pure.inspect_term t with
                         | Pulse_Syntax_Pure.Tm_ExistsSL (uu___, b, body) ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (69))
                                        (Prims.of_int (10))
                                        (Prims.of_int (75))
                                        (Prims.of_int (27)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (67))
                                        (Prims.of_int (31))
                                        (Prims.of_int (83))
                                        (Prims.of_int (39)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match Pulse_Syntax_Pure.inspect_term w
                                     with
                                     | Pulse_Syntax_Pure.Tm_Unknown ->
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
                                                       (Prims.of_int (76))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (76))
                                                       (Prims.of_int (42)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.fst"
                                                       (Prims.of_int (76))
                                                       (Prims.of_int (45))
                                                       (Prims.of_int (83))
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
                                                                  (Prims.of_int (77))
                                                                  (Prims.of_int (31))
                                                                  (Prims.of_int (77))
                                                                  (Prims.of_int (60)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (76))
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (83))
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
                                  (Pulse_RuntimeUtils.range_of_term t))
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
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (89))
                 (Prims.of_int (43)) (Prims.of_int (89)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (87))
                 (Prims.of_int (28)) (Prims.of_int (113)) (Prims.of_int (10)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> t.Pulse_Syntax_Base.term1))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | Pulse_Syntax_Base.Tm_IntroExists
                  { Pulse_Syntax_Base.p5 = p;
                    Pulse_Syntax_Base.witnesses = ws;_}
                  ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (91)) (Prims.of_int (36))
                                (Prims.of_int (91)) (Prims.of_int (65)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (89)) (Prims.of_int (52))
                                (Prims.of_int (113)) (Prims.of_int (10)))))
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
                                                             Pulse_Syntax_Base.t
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
                                                                    ((Pulse_Syntax_Base.mk_binder_ppname
                                                                    ty ppname)
                                                                    ::
                                                                    binders);
                                                                    Pulse_Syntax_Base.t
                                                                    = t1
                                                                  });
                                                             Pulse_Syntax_Base.range1
                                                               =
                                                               ((Pulse_Syntax_Naming.close_st_term'
                                                                   e x
                                                                   Prims.int_zero).Pulse_Syntax_Base.range1);
                                                             Pulse_Syntax_Base.effect_tag
                                                               =
                                                               ((Pulse_Syntax_Naming.close_st_term'
                                                                   e x
                                                                   Prims.int_zero).Pulse_Syntax_Base.effect_tag)
                                                           })) new_names
                                             {
                                               Pulse_Syntax_Base.term1 =
                                                 (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                    {
                                                      Pulse_Syntax_Base.hint_type
                                                        =
                                                        (Pulse_Syntax_Base.ASSERT
                                                           {
                                                             Pulse_Syntax_Base.p
                                                               = opened_p
                                                           });
                                                      Pulse_Syntax_Base.binders
                                                        = [];
                                                      Pulse_Syntax_Base.t =
                                                        {
                                                          Pulse_Syntax_Base.term1
                                                            =
                                                            (Pulse_Syntax_Base.Tm_IntroExists
                                                               {
                                                                 Pulse_Syntax_Base.p5
                                                                   = p;
                                                                 Pulse_Syntax_Base.witnesses
                                                                   = new_ws
                                                               });
                                                          Pulse_Syntax_Base.range1
                                                            =
                                                            (t.Pulse_Syntax_Base.range1);
                                                          Pulse_Syntax_Base.effect_tag
                                                            =
                                                            (t.Pulse_Syntax_Base.effect_tag)
                                                        }
                                                    });
                                               Pulse_Syntax_Base.range1 =
                                                 (t.Pulse_Syntax_Base.range1);
                                               Pulse_Syntax_Base.effect_tag =
                                                 (Pulse_Syntax_Base.as_effect_hint
                                                    Pulse_Syntax_Base.STT_Ghost)
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
                   (Prims.of_int (118)) (Prims.of_int (14))
                   (Prims.of_int (118)) (Prims.of_int (48)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (119)) (Prims.of_int (2))
                   (Prims.of_int (138)) (Prims.of_int (66)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_RuntimeUtils.range_of_term t))
          (fun uu___ ->
             (fun t_rng ->
                match ws with
                | [] ->
                    Obj.magic
                      (Pulse_Typing_Env.fail g
                         (FStar_Pervasives_Native.Some t_rng)
                         "intro exists with empty witnesses")
                | w::[] ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (122)) (Prims.of_int (13))
                                  (Prims.of_int (122)) (Prims.of_int (27)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (123)) (Prims.of_int (4))
                                  (Prims.of_int (125)) (Prims.of_int (64)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> Pulse_Syntax_Pure.inspect_term t))
                         (fun uu___ ->
                            (fun tv ->
                               if Pulse_Syntax_Pure.uu___is_Tm_ExistsSL tv
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            Pulse_Typing.wtag
                                              (FStar_Pervasives_Native.Some
                                                 Pulse_Syntax_Base.STT_Ghost)
                                              (Pulse_Syntax_Base.Tm_IntroExists
                                                 {
                                                   Pulse_Syntax_Base.p5 = t;
                                                   Pulse_Syntax_Base.witnesses
                                                     = [w]
                                                 }))))
                               else
                                 Obj.magic
                                   (Obj.repr
                                      (Pulse_Typing_Env.fail g
                                         (FStar_Pervasives_Native.Some t_rng)
                                         "intro exists with non-existential")))
                              uu___))
                | w::ws1 ->
                    (match Pulse_Syntax_Pure.inspect_term t with
                     | Pulse_Syntax_Pure.Tm_ExistsSL (u, b, body) ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (129))
                                       (Prims.of_int (17))
                                       (Prims.of_int (129))
                                       (Prims.of_int (43)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (129))
                                       (Prims.of_int (46))
                                       (Prims.of_int (136))
                                       (Prims.of_int (34)))))
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
                                                  (Prims.of_int (130))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (130))
                                                  (Prims.of_int (56)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (136))
                                                  (Prims.of_int (34)))))
                                         (Obj.magic
                                            (transform_to_unary_intro_exists
                                               g body1 ws1))
                                         (fun st ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___ ->
                                                 Pulse_Typing.wtag
                                                   FStar_Pervasives_Native.None
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
                                                          (Pulse_Typing.wtag
                                                             FStar_Pervasives_Native.None
                                                             (Pulse_Syntax_Base.Tm_IntroExists
                                                                {
                                                                  Pulse_Syntax_Base.p5
                                                                    = t;
                                                                  Pulse_Syntax_Base.witnesses
                                                                    = 
                                                                    [w]
                                                                }))
                                                      }))))) uu___))
                     | uu___ ->
                         Obj.magic
                           (Pulse_Typing_Env.fail g
                              (FStar_Pervasives_Native.Some t_rng)
                              "intro exists with non-existential"))) uu___)
let rec (check : Pulse_Checker_Base.check_t) =
  fun g0 ->
    fun pre0 ->
      fun pre0_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              if Pulse_Checker_AssertWithBinders.handle_head_immediately t
              then
                Pulse_Checker_AssertWithBinders.check g0 pre0 () post_hint
                  res_ppname t check
              else
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (153)) (Prims.of_int (6))
                           (Prims.of_int (153)) (Prims.of_int (59)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.fst"
                           (Prims.of_int (151)) (Prims.of_int (7))
                           (Prims.of_int (290)) (Prims.of_int (3)))))
                  (Obj.magic
                     (Pulse_Checker_Prover.elim_exists_and_pure g0 pre0 ()))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Pervasives.Mkdtuple4
                            (g, pre, pre_typing, k_elim_pure) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (156))
                                          (Prims.of_int (4))
                                          (Prims.of_int (162))
                                          (Prims.of_int (59)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (162))
                                          (Prims.of_int (60))
                                          (Prims.of_int (289))
                                          (Prims.of_int (52)))))
                                 (if
                                    Pulse_RuntimeUtils.debug_at_level
                                      (Pulse_Typing_Env.fstar_env g)
                                      "pulse.checker"
                                  then
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (157))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (162))
                                                     (Prims.of_int (59)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (157))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (162))
                                                     (Prims.of_int (59)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (162))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (162))
                                                           (Prims.of_int (58)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (157))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (162))
                                                           (Prims.of_int (59)))))
                                                  (Obj.magic
                                                     (Pulse_Syntax_Printer.st_term_to_string
                                                        t))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (57)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                   (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    pre))
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Env.env_to_string
                                                                    g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (Pulse_RuntimeUtils.print_context
                                                                    (Pulse_Typing_Env.get_context
                                                                    g)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    t.Pulse_Syntax_Base.range1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    fun x3 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "At "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "{\nerr context:\n>"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n\n{\n\tenv="))
                                                                    (Prims.strcat
                                                                    x1
                                                                    "\ncontext:\n"))
                                                                    (Prims.strcat
                                                                    x2
                                                                    ",\n\nst_term: "))
                                                                    (Prims.strcat
                                                                    x3 "}}\n")))))
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    uu___3
                                                                    uu___2))))
                                                       uu___2)))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_V2_Builtins.print
                                                       uu___2)) uu___2)))
                                  else
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 -> ()))))
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (164))
                                                     (Prims.of_int (46))
                                                     (Prims.of_int (285))
                                                     (Prims.of_int (50)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (286))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (289))
                                                     (Prims.of_int (52)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (165))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (165))
                                                           (Prims.of_int (57)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (166))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (285))
                                                           (Prims.of_int (50)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        Pulse_Checker_Pure.push_context
                                                          (Pulse_Syntax_Printer.tag_of_st_term
                                                             t)
                                                          t.Pulse_Syntax_Base.range1
                                                          g))
                                                  (fun uu___3 ->
                                                     (fun g1 ->
                                                        match t.Pulse_Syntax_Base.term1
                                                        with
                                                        | Pulse_Syntax_Base.Tm_Return
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Return.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_Abs
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_V2_Derived.fail
                                                                    "Tm_Abs check should not have been called in the checker"))
                                                        | Pulse_Syntax_Base.Tm_STApp
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_STApp.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                        | Pulse_Syntax_Base.Tm_ElimExists
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Exists.check_elim_exists
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                        | Pulse_Syntax_Base.Tm_IntroExists
                                                            {
                                                              Pulse_Syntax_Base.p5
                                                                = p;
                                                              Pulse_Syntax_Base.witnesses
                                                                = witnesses;_}
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (48)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (58)))))
                                                                    (
                                                                    Obj.magic
                                                                    (instantiate_unknown_witnesses
                                                                    g1 t))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t1 ->
                                                                    Obj.magic
                                                                    (check g1
                                                                    pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t1)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match witnesses
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "intro exists with empty witnesses")
                                                                    | 
                                                                    uu___4::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Exists.check_intro_exists
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (transform_to_unary_intro_exists
                                                                    g1 p
                                                                    witnesses))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (check g1
                                                                    pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t1))
                                                                    uu___5))))
                                                                    uu___3)))
                                                        | Pulse_Syntax_Base.Tm_Bind
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Bind.check_bind
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_TotBind
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Bind.check_tot_bind
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_If
                                                            {
                                                              Pulse_Syntax_Base.b1
                                                                = b;
                                                              Pulse_Syntax_Base.then_
                                                                = e1;
                                                              Pulse_Syntax_Base.else_
                                                                = e2;
                                                              Pulse_Syntax_Base.post1
                                                                = post_if;_}
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (97)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    match 
                                                                    (post_if,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    p,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Base.intro_post_hint
                                                                    g1
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    FStar_Pervasives_Native.None
                                                                    p))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    p,
                                                                    FStar_Pervasives_Native.Some
                                                                    q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (60)))))
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
                                                                    q.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Multiple annotated postconditions---remove one of them.\nThe context expects the postcondition "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ",\nbut this conditional was annotated with postcondition "))
                                                                    (Prims.strcat
                                                                    x "")))))
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
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3)))
                                                                    | 
                                                                    (uu___3,
                                                                    uu___4)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\nEither annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_If.check
                                                                    g1 pre ()
                                                                    post
                                                                    res_ppname
                                                                    b e1 e2
                                                                    check))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
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
                                                                    uu___3)))
                                                        | Pulse_Syntax_Base.Tm_While
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_While.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_Match
                                                            {
                                                              Pulse_Syntax_Base.sc
                                                                = sc;
                                                              Pulse_Syntax_Base.returns_
                                                                = post_match;
                                                              Pulse_Syntax_Base.brs
                                                                = brs;_}
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (97)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (32)))))
                                                                    (
                                                                    match 
                                                                    (post_match,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    p,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Base.intro_post_hint
                                                                    g1
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    FStar_Pervasives_Native.None
                                                                    p))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    p,
                                                                    FStar_Pervasives_Native.Some
                                                                    q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (60)))))
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
                                                                    q.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Multiple annotated postconditions---remove one of them.\nThe context expects the postcondition "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ",\nbut this conditional was annotated with postcondition "))
                                                                    (Prims.strcat
                                                                    x "")))))
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
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3)))
                                                                    | 
                                                                    (uu___3,
                                                                    uu___4)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\nEither annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Match.check
                                                                    g1 pre ()
                                                                    post
                                                                    res_ppname
                                                                    sc brs
                                                                    check))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    pre',
                                                                    g11, k)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    pre',
                                                                    g11, k)))))
                                                                    uu___3)))
                                                        | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_AssertWithBinders.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_WithLocal
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_WithLocal.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_WithLocalArray
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_WithLocalArray.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_Par
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Par.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | Pulse_Syntax_Base.Tm_IntroPure
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_IntroPure.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                        | Pulse_Syntax_Base.Tm_Admit
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Admit.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                        | Pulse_Syntax_Base.Tm_Unreachable
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Unreachable.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                        | Pulse_Syntax_Base.Tm_Rewrite
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_Rewrite.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                        | Pulse_Syntax_Base.Tm_WithInv
                                                            uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Checker_WithInv.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                        | uu___3 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_V2_Derived.fail
                                                                    "Checker form not implemented")))
                                                       uu___3)))
                                            (fun r ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    match r with
                                                    | FStar_Pervasives.Mkdtuple5
                                                        (x, g1, t1, pre', k)
                                                        ->
                                                        FStar_Pervasives.Mkdtuple5
                                                          (x, g1, t1, pre',
                                                            (Pulse_Checker_Base.k_elab_trans
                                                               g0 g g1 pre0
                                                               pre
                                                               (FStar_Pervasives.dfst
                                                                  pre')
                                                               k_elim_pure k))))))
                                      uu___2))) uu___1)